// Allow JSONRPCServer to be derived for a trait using the '#[jsonrpc_server]' macro.

#![recursion_limit = "256"]

extern crate proc_macro;
use proc_macro2;
use proc_macro2::Span;
use quote::quote;
use syn::spanned::Spanned;
use syn::{
	parse_macro_input, ArgSelfRef, FnArg, FnDecl, Ident, ItemTrait, MethodSig, Pat, PatIdent,
	TraitItem, Type,
};

#[proc_macro_attribute]
pub fn jsonrpc_server(
	_: proc_macro::TokenStream,
	item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
	let trait_def = parse_macro_input!(item as ItemTrait);
	let server_impl = match impl_server(&trait_def) {
		Ok(s) => s,
		Err(reject) => {
			for r in reject {
				r.raise();
			}
			return proc_macro::TokenStream::new();
		}
	};
	proc_macro::TokenStream::from(quote! {
		#trait_def
		#server_impl
	})
}

// Generate a JSONRPCServer implementation for types. Types are asummed to implement tr
fn impl_server(
	tr: &ItemTrait //	types: &[proc_macro2::Ident]
) -> Result<proc_macro2::TokenStream, Vec<Rejection>> {
	let trait_name = &tr.ident;
	let methods: Vec<&MethodSig> = trait_methods(&tr)?;

	for method in methods.iter() {
		if method.ident.to_string().starts_with("rpc.") {
			Err(Rejection::create(
				method.ident.span(),
				Reason::ReservedMethodPrefix,
			))?;
		}
	}

	let handlers = methods.iter().map(|method| {
		let method_literal = method.ident.to_string();
		let handler = add_handler(trait_name, method)?;
		Ok(quote! { #method_literal => jsonrpc::try_serialize(& #handler) })
	});
	let handlers: Vec<proc_macro2::TokenStream> = aggregate_errs(partition(handlers))?;

	Ok(quote! {
		impl jsonrpc::JSONRPCServer for dyn #trait_name {
			fn handle(&self, method: &str, params: jsonrpc::Params)
					  -> Result<jsonrpc::Value, jsonrpc::Error> {
				match method {
					#(#handlers,)*
					_ => Err(jsonrpc::Error::method_not_found()),
				}
			}
		}
	})
}

// return all methods in the trait, or reject if trait contains an item that is not a method
fn trait_methods<'a>(tr: &'a ItemTrait) -> Result<Vec<&'a MethodSig>, Rejection> {
	tr.items
		.iter()
		.map(|item| match item {
			TraitItem::Method(method) => Ok(&method.sig),
			other => Err(Rejection::create(
				other.span(),
				Reason::TraitNotStrictlyMethods,
			)),
		})
		.collect()
}

fn add_handler(
	trait_name: &Ident,
	method: &MethodSig,
) -> Result<proc_macro2::TokenStream, Vec<Rejection>> {
	let method_name = &method.ident;
	let args = get_args(&method.decl)?;
	let arg_name_literals = args.iter().map(|(id, _)| id.to_string());
	let parse_args = args.iter().enumerate().map(|(index, (ident, _))| {
		let argname_literal = format!("\"{}\"", ident);
		quote! {{
			let next_arg = ordered_args.next().expect(
				"RPC method Got too few args. This is a bug." // checked in get_rpc_args
			);
			jsonrpc::serde_json::from_value(next_arg).map_err(|_| {
				jsonrpc::InvalidArgs::InvalidArgStructure {
					name: #argname_literal,
					index: #index,
				}.into()
			})?
		}}
	});

	Ok(quote! {{
		let mut args: Vec<jsonrpc::Value> =
			jsonrpc::get_rpc_args(&[#(#arg_name_literals),*], params)
			.map_err(|a| a.into())?;

		let mut ordered_args = args.drain(..);

		// call the target procedure
		let res = <#trait_name>::#method_name(self, #(#parse_args),*);

		res
	}})
}

// Get the name and type of each argument from method. Skip the first argument, which must be &self.
// If the first argument is not &self, an error will be returned.
fn get_args<'a>(method: &'a FnDecl) -> Result<Vec<(&'a Ident, &'a Type)>, Vec<Rejection>> {
	let mut inputs = method.inputs.iter();
	match inputs.next() {
		Some(FnArg::SelfRef(ArgSelfRef {
			mutability: None, ..
		})) => Ok(()),
		Some(a) => Err(Rejection::create(a.span(), Reason::FirstArgumentNotSelfRef)),
		None => Err(Rejection::create(
			method.inputs.span(),
			Reason::FirstArgumentNotSelfRef,
		)),
	}?;
	partition(inputs.map(as_jsonrpc_arg))
}

// If all Ok, return Vec of successful values, otherwise return Vec of errors.
fn partition<K, E, I: Iterator<Item = Result<K, E>>>(iter: I) -> Result<Vec<K>, Vec<E>> {
	let (min, _) = iter.size_hint();
	let mut oks: Vec<K> = Vec::with_capacity(min);
	let mut errs: Vec<E> = Vec::new();
	for i in iter {
		match i {
			Ok(ok) => oks.push(ok),
			Err(err) => errs.push(err),
		}
	}
	if errs.is_empty() {
		Ok(oks)
	} else {
		Err(errs)
	}
}

fn as_jsonrpc_arg(arg: &FnArg) -> Result<(&Ident, &Type), Rejection> {
	let arg = match arg {
		FnArg::Captured(captured) => Ok(captured),
		a => Err(Rejection::create(a.span(), Reason::ConcreteTypesRequired)),
	}?;
	let ty = &arg.ty;
	let pat_ident = match &arg.pat {
		Pat::Ident(pat_ident) => Ok(pat_ident),
		Pat::Ref(r) => Err(Rejection::create(r.span(), Reason::ReferenceArg)),
		a => Err(Rejection::create(a.span(), Reason::PatternMatchedArg)),
	}?;
	let ident = match pat_ident {
		PatIdent {
			by_ref: Some(r), ..
		} => Err(Rejection::create(r.span(), Reason::ReferenceArg)),
		PatIdent {
			mutability: Some(m),
			..
		} => Err(Rejection::create(m.span(), Reason::MutableArg)),
		PatIdent {
			subpat: Some((l, _)),
			..
		} => Err(Rejection::create(l.span(), Reason::PatternMatchedArg)),
		PatIdent {
			ident,
			by_ref: None,
			mutability: None,
			subpat: None,
		} => Ok(ident),
	}?;
	Ok((&ident, &ty))
}

struct Rejection {
	span: Span,
	reason: Reason,
}

enum Reason {
	FirstArgumentNotSelfRef,
	PatternMatchedArg,
	ConcreteTypesRequired,
	TraitNotStrictlyMethods,
	ReservedMethodPrefix,
	ReferenceArg,
	MutableArg,
}

impl Rejection {
	// Unfortunately syn's neat error reporting capabilities don't work on stable.
	// If 'proc_macro_diagnostic' support does land on stable, we can add nicer error reporting,
	// like:
	//
	// match item {
	//     TraitItem::Method(method) => methods.push(*method),
	// 	   other => {
	//         other
	//             .span()
	//             .unstable()
	//             .error("Macro 'jsonrpc_server' expects a trait containing methods only.")
	//             .emit();
	//         return TokenStream::new();
	//     }
	// }
	//
	// more info: https://github.com/rust-lang/rust/issues/54140
	fn create(span: Span, reason: Reason) -> Self {
		Rejection { span, reason }
	}

	// For now, we'll panic with an error message. When #![feature(proc_macro_diagnostic)]
	// becomes available, we'll be able to output pretty errors just like rustc!
	fn raise(self) {
		let description = match self.reason {
			Reason::FirstArgumentNotSelfRef => "First argument to jsonrpc method must be &self.",
			Reason::PatternMatchedArg => {
				"Pattern matched arguments are not supported in jsonrpc methods."
			}
			Reason::ConcreteTypesRequired => {
				"Arguments and return values must have concrete types."
			}
			Reason::TraitNotStrictlyMethods => {
				"Macro 'jsonrpc_server' expects trait definition containing methods only."
			}
			Reason::ReservedMethodPrefix => {
				"The prefix 'rpc.' is reserved https://www.jsonrpc.org/specification#request_object"
			}
			Reason::ReferenceArg => "Reference arguments not supported in jsonrpc macro.",
			Reason::MutableArg => "Mutable arguments not supported in jsonrpc macro.",
		};
		panic!("{:?} {}", self.span, description);
	}
}

impl From<Rejection> for Vec<Rejection> {
	fn from(r: Rejection) -> Vec<Rejection> {
		vec![r]
	}
}

fn aggregate_errs<K, E>(r: Result<K, Vec<Vec<E>>>) -> Result<K, Vec<E>> {
	match r {
		Err(mut e) => Err(e.drain(..).flatten().collect()),
		Ok(a) => Ok(a),
	}
}
