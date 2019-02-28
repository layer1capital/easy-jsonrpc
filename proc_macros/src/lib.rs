// Allow JSONRPCServer to be derived for a trait using the '#[jsonrpc_server]' macro.

#![recursion_limit = "256"]

extern crate proc_macro;
use heck::SnakeCase;
use proc_macro2::{self, Span};
use quote::{quote, quote_spanned};
use syn::{
    parse_macro_input, punctuated::Punctuated, spanned::Spanned, token::Paren, ArgSelfRef, FnArg,
    FnDecl, Ident, ItemTrait, MethodSig, Pat, PatIdent, ReturnType, TraitItem, Type, TypeTuple,
};

#[deprecated(since="0.1.5", note="please use `rpc` instead")]
#[proc_macro_attribute]
pub fn jsonrpc_server(
    _: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let trait_def = parse_macro_input!(item as ItemTrait);
    let server_impl = raise_if_err(impl_server(&trait_def));
    proc_macro::TokenStream::from(quote! {
        #trait_def
        #server_impl
    })
}

#[proc_macro_attribute]
pub fn rpc(_: proc_macro::TokenStream, item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let trait_def = parse_macro_input!(item as ItemTrait);
    let server_impl = raise_if_err(impl_server(&trait_def));
    let client_impl = raise_if_err(impl_client(&trait_def));
    proc_macro::TokenStream::from(quote! {
        #trait_def
        #server_impl
        #client_impl
    })
}

// if Ok, return token stream, else report error
fn raise_if_err(res: Result<proc_macro2::TokenStream, Rejections>) -> proc_macro2::TokenStream {
    match res {
        Ok(stream) => stream,
        Err(rej) => rej.raise(),
    }
}

// generate a JSONRPCServer implementation for &dyn Trait
fn impl_server(tr: &ItemTrait) -> Result<proc_macro2::TokenStream, Rejections> {
    let trait_name = &tr.ident;
    let methods: Vec<&MethodSig> = trait_methods(&tr)?;

    let handlers = methods.iter().map(|method| {
        let method_literal = method.ident.to_string();
        let method_return_type_span = return_type_span(&method);
        let handler = add_handler(trait_name, method)?;
        let try_serialize = quote_spanned! {method_return_type_span =>
        easy_jsonrpc::try_serialize(&result)};
        Ok(quote! { #method_literal => {
            let result = #handler;
            #try_serialize
        }})
    });
    let handlers: Vec<proc_macro2::TokenStream> = partition(handlers)?;

    Ok(quote! {
        impl easy_jsonrpc::JSONRPCServer for dyn #trait_name {
            fn handle(&self, method: &str, params: easy_jsonrpc::Params)
                      -> Result<easy_jsonrpc::Value, easy_jsonrpc::Error> {
                match method {
                    #(#handlers,)*
                    _ => Err(easy_jsonrpc::Error::method_not_found()),
                }
            }
        }
    })
}

fn impl_client(tr: &ItemTrait) -> Result<proc_macro2::TokenStream, Rejections> {
    let trait_name = &tr.ident;
    let methods: Vec<&MethodSig> = trait_methods(&tr)?;
    let mod_name = Ident::new(&trait_name.to_string().to_snake_case(), Span::call_site());
    let method_impls = methods
        .iter()
        .map(|method| impl_client_method(*method))
        .collect::<Result<Vec<proc_macro2::TokenStream>, Rejections>>()?;

    Ok(quote! {
        mod #mod_name {
            use super::easy_jsonrpc::*;

            #(#method_impls)*
        }
    })
}

fn impl_client_method(method: &MethodSig) -> Result<proc_macro2::TokenStream, Rejections> {
    let method_name = &method.ident;
    let method_name_literal = &method_name.to_string();
    let args = get_args(&method.decl)?;
    let fn_definition_args: &Vec<_> = &args
        .iter()
        .enumerate()
        .map(|(i, (name, typ))| {
            let arg_num_name = Ident::new(&format!("arg{}", i), name.span());
            quote! {#arg_num_name: #typ}
        })
        .collect();
    let args_serialize: &Vec<_> = &args
        .iter()
        .enumerate()
        .map(|(i, (name, _))| {
            let arg_num_name = Ident::new(&format!("arg{}", i), name.span());
            quote! {
                serde_json::to_value(#arg_num_name).map_err(|_| ArgSerializeError)?
            }
        })
        .collect();
    let return_typ = return_type(&method);

    Ok(quote! {
        #[allow(non_camel_case_types)]
        pub struct #method_name {
            id: u64,
        }

        impl #method_name {
            // calls with random id
            pub fn call(
                #(#fn_definition_args),*
            ) -> Result<(Call<'static>, Self), ArgSerializeError> {
                let id = rand::random::<u64>();
                let mc = Call {
                    id: Some(id),
                    method: #method_name_literal,
                    args: vec![
                        #(#args_serialize),*
                    ],
                };
                Ok((mc, Self { id }))
            }

            pub fn notification(
                #(#fn_definition_args),*
            ) -> Result<Call<'static>, ArgSerializeError> {
                Ok(Call {
                    id: None,
                    method: #method_name_literal,
                    args: vec![
                        #(#args_serialize),*
                    ],
                })
            }

            /// Get typed return value from server response.
            /// If response contains the return value for this request, remove it from the
            /// server response, attempt to interpret the return value as a typed value.
            pub fn get_return(
                &self,
                response: &mut Response,
            ) -> Result<#return_typ, ResponseFail> {
                response
                    .remove(self.id)
                    .ok_or(ResponseFail::ResultNotFound)
                    .and_then(|result| result.map_err(ResponseFail::RpcError))
                    .and_then(|raw_return| {
                        <#return_typ>::deserialize(&raw_return)
                            .map_err(|_| ResponseFail::InvalidResponse)
                    })
            }
        }
    })
}

fn return_type_span(method: &MethodSig) -> Span {
    let return_type = match &method.decl.output {
        ReturnType::Default => None,
        ReturnType::Type(_, typ) => Some(typ),
    };
    return_type
        .map(|typ| typ.span())
        .unwrap_or_else(|| method.decl.output.span().clone())
}

fn return_type(method: &MethodSig) -> Type {
    match &method.decl.output {
        ReturnType::Default => Type::Tuple(TypeTuple {
            paren_token: Paren {
                span: method.decl.output.span(),
            },
            elems: Punctuated::new(),
        }),
        ReturnType::Type(_, typ) => *typ.clone(),
    }
}

// return all methods in the trait, or reject if trait contains an item that is not a method
fn trait_methods<'a>(tr: &'a ItemTrait) -> Result<Vec<&'a MethodSig>, Rejections> {
    let methods = partition(tr.items.iter().map(|item| match item {
        TraitItem::Method(method) => Ok(&method.sig),
        other => Err(Rejection::create(other.span(), Reason::TraitNotStrictlyMethods).into()),
    }))?;
    partition(methods.iter().map(|method| {
        if method.ident.to_string().starts_with("rpc.") {
            Err(Rejection::create(method.ident.span(), Reason::ReservedMethodPrefix).into())
        } else {
            Ok(())
        }
    }))?;
    Ok(methods)
}

// generate code that parses rpc arguments and calls the given method
fn add_handler(
    trait_name: &Ident,
    method: &MethodSig,
) -> Result<proc_macro2::TokenStream, Rejections> {
    let method_name = &method.ident;
    let args = get_args(&method.decl)?;
    let arg_name_literals = args.iter().map(|(id, _)| id.to_string());
    let parse_args = args.iter().enumerate().map(|(index, (ident, ty))| {
        let argname_literal = format!("\"{}\"", ident);
        // non-lexical lifetimes make it possible to create a reference to an anonymous owned value
        let prefix = match ty {
            syn::Type::Reference(_) => quote! { & },
            _ => quote! {},
        };
        quote_spanned! { ty.span() => #prefix {
            let next_arg = ordered_args.next().expect(
                "RPC method Got too few args. This is a bug." // checked in get_rpc_args
            );
            easy_jsonrpc::serde_json::from_value(next_arg).map_err(|_| {
                easy_jsonrpc::InvalidArgs::InvalidArgStructure {
                    name: #argname_literal,
                    index: #index,
                }.into()
            })?
        }}
    });

    Ok(quote! {{
        let mut args: Vec<easy_jsonrpc::Value> =
            params.get_rpc_args(&[#(#arg_name_literals),*])
                .map_err(|a| a.into())?;
        let mut ordered_args = args.drain(..);
        let res = <#trait_name>::#method_name(self, #(#parse_args),*); // call the target procedure
        debug_assert_eq!(ordered_args.next(), None); // parse_args must consume ordered_args
        res
    }})
}

// Get the name and type of each argument from method. Skip the first argument, which must be &self.
// If the first argument is not &self, an error will be returned.
fn get_args<'a>(method: &'a FnDecl) -> Result<Vec<(&'a Ident, &'a Type)>, Rejections> {
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

// If all Ok, return Vec of successful values, otherwise return all Rejections.
fn partition<K, I: Iterator<Item = Result<K, Rejections>>>(iter: I) -> Result<Vec<K>, Rejections> {
    let (min, _) = iter.size_hint();
    let mut oks: Vec<K> = Vec::with_capacity(min);
    let mut errs: Vec<Rejection> = Vec::new();
    for i in iter {
        match i {
            Ok(ok) => oks.push(ok),
            Err(Rejections { first, rest }) => {
                errs.push(first);
                errs.extend(rest);
            }
        }
    }
    match errs.first() {
        Some(first) => Err(Rejections {
            first: *first,
            rest: errs[1..].to_vec(),
        }),
        None => Ok(oks),
    }
}

// Attempt to extract name and type from arg
fn as_jsonrpc_arg(arg: &FnArg) -> Result<(&Ident, &Type), Rejections> {
    let arg = match arg {
        FnArg::Captured(captured) => Ok(captured),
        a => Err(Rejection::create(a.span(), Reason::ConcreteTypesRequired)),
    }?;
    let ty = &arg.ty;
    let pat_ident = match &arg.pat {
        Pat::Ident(pat_ident) => Ok(pat_ident),
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

// returned when macro input is invalid
#[derive(Clone, Copy)]
struct Rejection {
    span: Span,
    reason: Reason,
}

// reason for a rejection, reason is comminicated to user when a rejection is returned
#[derive(Clone, Copy)]
enum Reason {
    FirstArgumentNotSelfRef,
    PatternMatchedArg,
    ConcreteTypesRequired,
    TraitNotStrictlyMethods,
    ReservedMethodPrefix,
    ReferenceArg,
    MutableArg,
}

// Rustc often reports whole batches of errors at once. We can do the same by returning lists of
// Rejections when appropriate.
struct Rejections {
    first: Rejection, // must contain least one rejection
    rest: Vec<Rejection>,
}

impl Rejections {
    // report all contained rejections
    fn raise(self) -> proc_macro2::TokenStream {
        let Rejections { first, mut rest } = self;
        let first_err = first.raise();
        let rest_err = rest.drain(..).map(Rejection::raise);
        quote! {
            #first_err
            #(#rest_err)*
        }
    }
}

// syn's neat error reporting capabilities let us provide helpful errors like the following:
//
// ```
// error: expected type, found `{`
// --> src/main.rs:1:14
//   |
// 1 | fn main() -> {
//   |              ^
// ```
impl Rejection {
    fn create(span: Span, reason: Reason) -> Self {
        Rejection { span, reason }
    }

    // generate a compile_err!() from self
    fn raise(self) -> proc_macro2::TokenStream {
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

        syn::Error::new(self.span, description).to_compile_error()
    }
}

impl From<Rejection> for Rejections {
    fn from(first: Rejection) -> Rejections {
        Rejections {
            first,
            rest: vec![],
        }
    }
}
