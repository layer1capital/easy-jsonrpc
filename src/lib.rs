/*!
# Easy jsonrpc

Generates rpc handlers based on a trait definition.

## Defining an api

```rust
use easy_jsonrpc;

#[easy_jsonrpc::rpc]
pub trait Adder {
    fn checked_add(&self, a: isize, b: isize) -> Option<isize>;
    fn wrapping_add(&self, a: isize, b: isize) -> isize;
    fn is_some(&self, a: Option<usize>) -> bool {
        a.is_some()
    }
    fn takes_ref(&self, rf: &isize);
}
```

The rpc macro generates
1. An implementaion of the Handler trait for &dyn Adder
2. A helper module for rpc clients

## Server side usage

```rust
# use easy_jsonrpc;
# #[easy_jsonrpc::rpc]
# pub trait Adder {
#     fn checked_add(&self, a: isize, b: isize) -> Option<isize>;
#     fn wrapping_add(&self, a: isize, b: isize) -> isize;
#     fn is_some(&self, a: Option<usize>) -> bool {
#         a.is_some()
#     }
#     fn takes_ref(&self, rf: &isize);
# }
use easy_jsonrpc::{Handler, MaybeReply};
use serde_json::json;

struct AdderImpl;

impl Adder for AdderImpl {
    fn checked_add(&self, a: isize, b: isize) -> Option<isize> { a.checked_add(b) }
    fn wrapping_add(&self, a: isize, b: isize) -> isize { a.wrapping_add(b) }
    fn takes_ref(&self, rf: &isize) {}
}

let handler = (&AdderImpl {} as &dyn Adder);

assert_eq!(
    handler.handle_request(json!({
        "jsonrpc": "2.0",
        "method": "wrapping_add",
        "params": [1, 2],
        "id": 1
    })),
    MaybeReply::Reply(json!({
        "jsonrpc": "2.0",
        "result": 3,
        "id": 1
    }))
);
```

## Client side usage

```rust
# use easy_jsonrpc;
# #[easy_jsonrpc::rpc]
# pub trait Adder {
#     fn checked_add(&self, a: isize, b: isize) -> Option<isize>;
#     fn wrapping_add(&self, a: isize, b: isize) -> isize;
#     fn is_some(&self, a: Option<usize>) -> bool;
#     fn takes_ref(&self, rf: &isize);
# }
# use easy_jsonrpc::{Handler, MaybeReply};
# use serde_json::json;
# struct AdderImpl;
# impl Adder for AdderImpl {
#     fn checked_add(&self, a: isize, b: isize) -> Option<isize> {
#         a.checked_add(b)
#     }
#    fn wrapping_add(&self, a: isize, b: isize) -> isize {
#        a.wrapping_add(b)
#    }
#    fn is_some(&self, a: Option<usize>) -> bool {
#        a.is_some()
#    }
#    fn takes_ref(&self, rf: &isize) {}
# }
# let handler = (&AdderImpl {} as &dyn Adder);
let bind = adder::checked_add(1, 2).unwrap();
let (call, tracker) = bind.call();
let json_response = match handler.handle_request(call.as_request()) {
   MaybeReply::Reply(resp) => resp,
   MaybeReply::DontReply => panic!(),
};
let mut response = easy_jsonrpc::Response::from_json_response(json_response).unwrap();
assert_eq!(tracker.get_return(&mut response).unwrap(), Some(3));
```

## Bonus bits

```rust
# use easy_jsonrpc;
# #[easy_jsonrpc::rpc]
# pub trait Adder {
#     fn checked_add(&self, a: isize, b: isize) -> Option<isize>;
#     fn wrapping_add(&self, a: isize, b: isize) -> isize;
#     fn is_some(&self, a: Option<usize>) -> bool;
#     fn takes_ref(&self, rf: &isize);
# }
# use easy_jsonrpc::{Handler, MaybeReply};
# use serde_json::json;
# struct AdderImpl;
# impl Adder for AdderImpl {
#     fn checked_add(&self, a: isize, b: isize) -> Option<isize> {
#         a.checked_add(b)
#     }
#    fn wrapping_add(&self, a: isize, b: isize) -> isize {
#        a.wrapping_add(b)
#    }
#    fn is_some(&self, a: Option<usize>) -> bool {
#        a.is_some()
#    }
#    fn takes_ref(&self, rf: &isize) {}
# }
# let handler = (&AdderImpl {} as &dyn Adder);
// Named arguments are handled for free
assert_eq!(
    handler.handle_request(json!({
        "jsonrpc": "2.0",
        "method": "wrapping_add",
        "params": {
            "a": 1,
            "b": 2
        },
        "id": 1
    })),
    MaybeReply::Reply(json!({
        "jsonrpc": "2.0",
        "result": 3,
        "id": 1
    }))
);

// Notifications (calls without an id) are handled sanely
assert_eq!(
    handler.handle_request(json!({
        "jsonrpc": "2.0",
        "method": "wrapping_add",
        "params": [1, 1]
    })),
    MaybeReply::DontReply
);

// Notification are easy to generate
let bind = adder::checked_add(0, 0).unwrap();
let notification = bind.notification().as_request();
assert_eq!(handler.handle_request(notification), MaybeReply::DontReply);

// Batch calls are possible
use easy_jsonrpc::Call;
let bind0 = adder::checked_add(0, 0).unwrap();
let (call0, tracker0) = bind0.call();
let bind1 = adder::checked_add(1, 0).unwrap();
let (call1, tracker1) = bind1.call();
let bind2 = adder::wrapping_add(1, 1).unwrap();
let (call2, tracker2) = bind2.call();
let bind3 = adder::wrapping_add(1, 1).unwrap();
let call3 = bind3.notification();
let json_request = Call::batch_request(&[call0, call1, call2, call3]);
let json_response = match handler.handle_request(json_request) {
   MaybeReply::Reply(resp) => resp,
   MaybeReply::DontReply => panic!(),
};
let mut response = easy_jsonrpc::Response::from_json_response(json_response).unwrap();
assert_eq!(tracker1.get_return(&mut response).unwrap(), Some(1));
assert_eq!(tracker0.get_return(&mut response).unwrap(), Some(0));
assert_eq!(tracker2.get_return(&mut response).unwrap(), 2);
```
 */

#![deny(missing_docs)]

const SERIALZATION_ERROR: i64 = -32000;

pub use easy_jsonrpc_proc_macro::rpc;

// used from generated code
#[doc(hidden)]
pub use jsonrpc_core::types::{
    self, Error, ErrorCode, Failure, Id, MethodCall, Notification, Output, Success, Version,
};
#[doc(hidden)]
use serde::de::Deserialize;
#[doc(hidden)]
pub use serde_json::{self, Value};

use rand;
use serde::ser::Serialize;
use serde_json::json;
use std::{collections::BTreeMap, marker::PhantomData};

/// Handles jsonrpc requests.
pub trait Handler {
    /// Type-check params and call method if method exists. This method is implemented automatically
    /// by the [rpc](../easy_jsonrpc_proc_macro/attr.rpc.html) macro.
    fn handle(&self, method: &str, params: Params) -> Result<Value, jsonrpc_core::Error>;

    /// Parses raw_request as a jsonrpc request, handles request according to the jsonrpc spec.
    fn handle_request(&self, raw_request: Value) -> MaybeReply {
        let request: jsonrpc_core::Request = match serde_json::from_value(raw_request) {
            Ok(request) => request,
            Err(_) => {
                return MaybeReply::Reply(serde_json::json!({
                    "jsonrpc": "2.0",
                    "error": {
                        "code": -32700,
                        "message": "Parse error"
                    },
                    "id": null
                }));
            }
        };
        let response = match handle_parsed_request(self, request) {
            Some(ret) => ret,
            None => return MaybeReply::DontReply,
        };
        MaybeReply::Reply(serde_json::to_value(response).unwrap_or_else(|e| {
            serde_json::json!({
                "jsonrpc": "2.0",
                "error": {
                    "code": SERIALZATION_ERROR,
                    "message": "Serialization error",
                    "data": format!("{}", e),
                },
                "id": null
            })
        }))
    }
}

/// Returned by Handler::handle_request
#[derive(Clone, PartialEq, Debug)]
pub enum MaybeReply {
    /// The value should be serialized and returned to the client.
    Reply(Value),
    /// The request consisted solely of notifications. No reply is necessary.
    DontReply,
}

impl MaybeReply {
    /// Convert to optional value.
    pub fn as_option(self) -> Option<Value> {
        match self {
            MaybeReply::Reply(val) => Some(val),
            MaybeReply::DontReply => None,
        }
    }
}

/// extract method name and parameters from call
/// if call is a normal method call, call `handle` and return result
/// if call is a notification, call `handle` and return None
/// if call is invalid return a jsonrpc failure
fn handle_call<S: ?Sized + Handler>(slef: &S, call: jsonrpc_core::Call) -> Option<Output> {
    let (method, params, maybe_id, version): (
        String,
        jsonrpc_core::Params,
        Option<Id>,
        Option<Version>,
    ) = match call {
        jsonrpc_core::Call::Invalid { id } => {
            return Some(Output::invalid_request(id, None));
        }
        jsonrpc_core::Call::MethodCall(MethodCall {
            method,
            params,
            id,
            jsonrpc,
        }) => (method, params, Some(id), jsonrpc),
        jsonrpc_core::Call::Notification(Notification {
            method,
            params,
            jsonrpc,
        }) => (method, params, None, jsonrpc),
    };
    let args = Params::from_rc_params(params);
    let ret = slef.handle(&method, args);
    let id = maybe_id?;
    Some(match ret {
        Ok(ok) => Output::Success(Success {
            jsonrpc: version,
            result: ok,
            id,
        }),
        Err(err) => Output::Failure(Failure {
            jsonrpc: version,
            error: err,
            id,
        }),
    })
}

// Handle a request after it has been successfuly deserialized, this function is private to avoid
// exposing jsonrpc_core types to the user. Also, it's not needed externally.
fn handle_parsed_request<S: ?Sized + Handler>(
    slef: &S,
    request: jsonrpc_core::Request,
) -> Option<jsonrpc_core::Response> {
    match request {
        jsonrpc_core::Request::Single(call) => {
            handle_call(slef, call).map(jsonrpc_core::Response::Single)
        }
        jsonrpc_core::Request::Batch(mut calls) => {
            let outputs = calls
                .drain(..)
                .filter_map(|call| handle_call(slef, call))
                .collect::<Vec<_>>();
            if outputs.is_empty() {
                None
            } else {
                Some(jsonrpc_core::Response::Batch(outputs))
            }
        }
    }
}

#[doc(hidden)]
pub enum InvalidArgs {
    WrongNumberOfArgs { expected: usize, actual: usize },
    ExtraNamedParameter { name: String },
    MissingNamedParameter { name: &'static str },
    InvalidArgStructure { name: &'static str, index: usize },
}

impl Into<Error> for InvalidArgs {
    fn into(self) -> Error {
        match self {
            InvalidArgs::WrongNumberOfArgs { expected, actual } => Error::invalid_params(format!(
                "WrongNumberOfArgs. Expected {}. Actual {}",
                expected, actual
            )),
            InvalidArgs::ExtraNamedParameter { name } => {
                Error::invalid_params(format!("ExtraNamedParameter {}", name))
            }
            InvalidArgs::MissingNamedParameter { name } => {
                Error::invalid_params(format!("MissingNamedParameter {}", name))
            }
            InvalidArgs::InvalidArgStructure { name, index } => Error::invalid_params(format!(
                "InvalidArgStructure {} at position {}.",
                name, index
            )),
        }
    }
}

/// Represetaion of jsonrpc arguments. Passing no arguments is assumed to be semantically equivalent
/// to passing 0 positional args, or passing a map with zero entries.
///
/// Users of this library will rarely need to deal with this type.
#[derive(Debug)]
pub enum Params {
    /// Arguments were either not present (expressed as a length 0 list), or arguments were provided as
    /// a json list.
    Positional(Vec<Value>),
    /// Arguments were provided as a json dictionary.
    Named(serde_json::Map<String, Value>),
}

impl Params {
    fn from_rc_params(params: jsonrpc_core::Params) -> Self {
        match params {
            jsonrpc_core::Params::Array(arr) => Params::Positional(arr),
            jsonrpc_core::Params::Map(map) => Params::Named(map),
            jsonrpc_core::Params::None => Params::Positional(vec![]),
        }
    }

    /// Verify and convert Params to an argument list. If arguments are provided as named
    /// parameters, interpret them as positional arguments using the names argument as a key.
    ///
    /// Verifies:
    ///    - Number of args in positional parameter list is correct
    ///    - No missing args in named parameter object
    ///    - No extra args in named parameter object
    pub fn get_rpc_args(self, names: &[&'static str]) -> Result<Vec<Value>, InvalidArgs> {
        debug_assert!(
            {
                fn contains_duplicates(list: &[&str]) -> bool {
                    (1..list.len()).any(|i| list[i..].contains(&list[i - 1]))
                }
                !contains_duplicates(names)
            },
            "get_rpc_args recieved duplicate argument names"
        );
        let ar: Vec<Value> = match self {
            Params::Positional(ar) => ar,
            Params::Named(mut ma) => {
                let mut ar: Vec<Value> = Vec::with_capacity(names.len());
                for name in names.iter() {
                    ar.push(
                        ma.remove(*name)
                            .ok_or(InvalidArgs::MissingNamedParameter { name })?,
                    );
                }
                debug_assert_eq!(ar.len(), names.len());
                match ma.keys().next() {
                    Some(key) => {
                        return Err(InvalidArgs::ExtraNamedParameter { name: key.clone() })
                    }
                    None => ar,
                }
            }
        };
        if ar.len() != names.len() {
            Err(InvalidArgs::WrongNumberOfArgs {
                expected: ar.len(),
                actual: names.len(),
            })
        } else {
            Ok(ar)
        }
    }
}

// Intentionally does not implement Serialize; we don't want users to accidentally send a call by
// itself. Does not implement clone because Vec<Value> is potentially expensive to clone.
/// Create a binding of arguments to a method name. Can be turned into either a jsonrpc call using
/// [call](#method.call), or a jsonrpc notification using [notification](#method.notification).
#[derive(Debug)]
pub struct BoundMethod<'a, T>
where
    T: Deserialize<'static>,
{
    method: &'a str,
    args: Vec<Value>,
    _spook: PhantomData<*const T>,
}

impl<'a, T> BoundMethod<'a, T>
where
    T: Deserialize<'static>,
{
    /// Create a binding of arguments to a method name.
    /// You probably don't want to use this method directly.
    /// Try using the rpc macro instead.
    pub fn new(method: &'a str, args: Vec<Value>) -> BoundMethod<T> {
        BoundMethod {
            method,
            args,
            _spook: PhantomData,
        }
    }

    /// Create a jsonrpc method call with a random id and a tracker for retrieving the return value.
    pub fn call(&'a self) -> (Call<'a>, Tracker<T>)
    where
        T: Deserialize<'static>,
    {
        let Self { method, args, .. } = self;
        let id = rand::random::<u64>();
        (
            Call {
                method,
                args,
                id: Some(id),
            },
            Tracker {
                id,
                _spook: PhantomData,
            },
        )
    }

    /// Create a jsonrpc method call with no id. Jsonrpc servers accept notifications silently.
    /// That is to say, they handle the notification, but send to reasponse.
    pub fn notification(&'a self) -> Call<'a> {
        let Self { method, args, .. } = self;
        Call {
            method,
            args,
            id: None,
        }
    }
}

// Intentionally does not implement Serialize; we don't want users to accidentally send a call by
// itself. Does not implement clone because Vec<Value> is potentially expensive to clone.
/// A single rpc method call with arguments. May be sent to the server by itself using
/// [as_request](#method.as_request), or as a batch, using
/// [batch_request](#method.batch_request).
pub struct Call<'a> {
    method: &'a str,
    args: &'a [Value],
    id: Option<u64>,
}

impl<'a> Call<'a> {
    /// Convert call to a json object which can be serialized and sent to a jsonrpc server.
    pub fn as_request(&self) -> Value {
        let Self { method, id, args } = self;
        match id {
            Some(id) => json!({
                "jsonrpc": "2.0",
                "method": method,
                "params": args,
                "id": id,
            }),
            None => json!({
                "jsonrpc": "2.0",
                "method": method,
                "params": args,
            }),
        }
    }

    /// Convert list of calls to a json object which can be serialized and sent to a jsonrpc server.
    pub fn batch_request(calls: &[Self]) -> Value {
        debug_assert!({
            fn contains_duplicates(list: &[u64]) -> bool {
                (1..list.len()).any(|i| list[i..].contains(&list[i - 1]))
            }
            let ids = calls.iter().filter_map(|call| call.id).collect::<Vec<_>>();
            !contains_duplicates(ids.as_slice())
        });
        Value::Array(calls.iter().map(Call::as_request).collect())
    }
}

/// used from generated code
#[doc(hidden)]
pub fn try_serialize<T: Serialize>(t: &T) -> Result<Value, Error> {
    // Serde serde_json::to_value does not perform io. It's still not safe to unwrap the result. For
    // example, the implementation of Serialize for Mutex returns an error if the mutex is poisined.
    // Another example, serialize(&std::Path) returns an error when it encounters invalid utf-8.
    serde_json::to_value(t).map_err(|e| Error {
        code: ErrorCode::ServerError(SERIALZATION_ERROR),
        message: "Serialization error".to_owned(),
        data: Some(Value::String(format!("{}", e))),
    })
}

/// Error returned when a tracker fails to retrive its response.
#[derive(Clone, PartialEq, Debug)]
pub enum ResponseFail {
    /// Server responded, but Server did not specify a result for the call in question.
    ResultNotFound,
    /// Server specified a result for the call in question, but it the result was malformed.
    InvalidResponse,
    /// Server specified a result for the call in question and the result was an rpc error.
    RpcError(Error),
}

/// Thrown when arguments fail to be serialized. Possible causes include, but are not limited to:
/// - A poisoned mutex
/// - A cstring containing invalid utf-8
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct ArgSerializeError;

/// Returned by [from_json_response](struct.Response.html#method.from_json_response) on error.
#[derive(Clone, PartialEq, Debug)]
pub enum InvalidResponse {
    /// Response is not a valid jsonrpc response.
    DeserailizeFailure,
    /// Response contains an id that is not number. The client helpers in easy_jsonrpc never send
    /// non-number ids, so if the server responds with a non-number id, something is wrong.
    ContainsNonNumericId,
}

/// Special purpose structure for holding a group of responses. Allows for response lookup by id.
/// Does not support non-number ids.
pub struct Response {
    /// Mapping from id to output of rpc call.
    pub outputs: BTreeMap<u64, Result<Value, Error>>,
}

impl Response {
    /// Deserialize response from a jsonrpc server.
    pub fn from_json_response(raw_jsonrpc_response: Value) -> Result<Self, InvalidResponse> {
        let response: jsonrpc_core::Response = serde_json::from_value(raw_jsonrpc_response)
            .map_err(|_| InvalidResponse::DeserailizeFailure)?;
        let mut calls: Vec<Output> = match response {
            jsonrpc_core::Response::Single(out) => vec![out],
            jsonrpc_core::Response::Batch(outs) => outs,
        };
        debug_assert!({
            fn contains_duplicates(list: &[u64]) -> bool {
                (1..list.len()).any(|i| list[i..].contains(&list[i - 1]))
            }
            let ids = calls
                .iter()
                .filter_map(|out| match out {
                    Output::Success(Success {
                        id: Id::Num(id), ..
                    })
                    | Output::Failure(Failure {
                        id: Id::Num(id), ..
                    }) => Some(*id),
                    _ => None,
                })
                .collect::<Vec<_>>();
            !contains_duplicates(ids.as_slice())
        });
        let outputs = calls
            .drain(..)
            .map(
                |out| -> Result<(u64, Result<Value, Error>), InvalidResponse> {
                    match out {
                        Output::Success(Success {
                            result,
                            id: Id::Num(id),
                            ..
                        }) => Ok((id, Ok(result))),
                        Output::Failure(Failure {
                            error,
                            id: Id::Num(id),
                            ..
                        }) => Ok((id, Err(error))),
                        _ => Err(InvalidResponse::ContainsNonNumericId),
                    }
                },
            )
            .collect::<Result<BTreeMap<u64, Result<Value, Error>>, InvalidResponse>>()?;
        Ok(Self { outputs })
    }

    /// Retrieve the output with a matching id and return it, return None if no such output exists.
    pub fn remove(&mut self, id: u64) -> Option<Result<Value, Error>> {
        self.outputs.remove(&id)
    }
}

/// Links a jsonrpc id to a return type.
/// Trackers can be used to get a typed return value from a json response.
pub struct Tracker<T>
where
    T: Deserialize<'static>,
{
    id: u64,
    _spook: PhantomData<*const T>,
}

impl<T> Tracker<T>
where
    T: Deserialize<'static>,
{
    /// Get typed return value from server response.
    /// If response contains the return value for this request, remove it from the
    /// server response and attempt to interpret it as a value with type T.
    pub fn get_return(&self, response: &mut Response) -> Result<T, ResponseFail> {
        let result = response
            .remove(self.id)
            .ok_or(ResponseFail::ResultNotFound)?;
        let raw_return = result.map_err(ResponseFail::RpcError)?;
        <T>::deserialize(raw_return).map_err(|_| ResponseFail::InvalidResponse)
    }
}

#[cfg(test)]
mod test {
    mod easy_jsonrpc {
        pub use crate::*;
    }
    use super::{Handler, MaybeReply};
    use jsonrpc_core;
    use serde_json::{json, Value};

    #[easy_jsonrpc::rpc]
    pub trait Adder {
        fn checked_add(&self, a: isize, b: isize) -> Option<isize>;
        fn wrapping_add(&self, a: isize, b: isize) -> isize;
        fn greet(&self) -> String;
        fn swallow(&self);
        fn repeat_list(&self, lst: Vec<usize>) -> Vec<usize>;
        fn fail(&self) -> Result<isize, String>;
        fn succeed(&self) -> Result<isize, String>;
        fn echo_ref(&self, a: &isize) -> isize;
    }

    struct AdderImpl;
    impl Adder for AdderImpl {
        fn checked_add(&self, a: isize, b: isize) -> Option<isize> {
            a.checked_add(b)
        }

        fn wrapping_add(&self, a: isize, b: isize) -> isize {
            a.wrapping_add(b)
        }

        fn greet(&self) -> String {
            "hello".into()
        }

        fn swallow(&self) {}

        fn repeat_list(&self, lst: Vec<usize>) -> Vec<usize> {
            let mut ret = lst.clone();
            ret.extend(lst);
            ret
        }

        fn fail(&self) -> Result<isize, String> {
            Err("tada!".into())
        }

        fn succeed(&self) -> Result<isize, String> {
            Ok(1)
        }

        fn echo_ref(&self, a: &isize) -> isize {
            *a
        }
    }

    fn assert_adder_response(request: Value, response: Value) {
        assert_eq!(
            (&AdderImpl {} as &dyn Adder)
                .handle_request(request)
                .as_option()
                .unwrap(),
            response
        );
    }

    fn error_code(request: Value) -> jsonrpc_core::ErrorCode {
        let raw_response = (&AdderImpl {} as &dyn Adder)
            .handle_request(request)
            .as_option()
            .unwrap();
        let response: jsonrpc_core::Response = serde_json::from_value(raw_response).unwrap();
        match response {
            jsonrpc_core::Response::Single(jsonrpc_core::Output::Failure(
                jsonrpc_core::Failure { error, .. },
            )) => error.code,
            _ => panic!(),
        }
    }

    #[test]
    fn batch() {
        assert_adder_response(
            json!([
                {
                    "jsonrpc": "2.0",
                    "method": "wrapping_add",
                    "params": [1, 1],
                    "id": 1
                },
                {
                    "jsonrpc": "2.0",
                    "method": "wrapping_add",
                    "params": [1, 2],
                    "id": 2
                },
                {
                    "jsonrpc": "2.0",
                    "method": "wrapping_add",
                    "params": [1, 3],
                    "id": null
                },
                {
                    "jsonrpc": "2.0",
                    "method": "wrapping_add",
                    "params": [1, 4],
                },
            ]),
            json!([
                {
                    "jsonrpc": "2.0",
                    "result": 2,
                    "id": 1
                },
                {
                    "jsonrpc": "2.0",
                    "result": 3,
                    "id": 2
                },
                {
                    "jsonrpc": "2.0",
                    "result": 4,
                    "id": null
                }
            ]),
        );
    }

    #[test]
    fn positional_args() {
        assert_adder_response(
            json!({
                "jsonrpc": "2.0",
                "method": "wrapping_add",
                "params": [1, 1],
                "id": 1
            }),
            json!({
                "jsonrpc": "2.0",
                "result": 2,
                "id": 1
            }),
        );
    }

    #[test]
    fn string_id() {
        assert_adder_response(
            json!({
                "jsonrpc": "2.0",
                "method": "wrapping_add",
                "params": [1, 1],
                "id": "jfjfks sasdfk"
            }),
            json!({
                "jsonrpc": "2.0",
                "result": 2,
                "id": "jfjfks sasdfk"
            }),
        );
        assert_adder_response(
            json!({
                "jsonrpc": "2.0",
                "method": "wrapping_add",
                "params": [1, 1],
                "id": ""
            }),
            json!({
                "jsonrpc": "2.0",
                "result": 2,
                "id": ""
            }),
        );
    }

    #[test]
    fn named_args() {
        assert_adder_response(
            json!({
                "jsonrpc": "2.0",
                "method": "wrapping_add",
                "params": {
                    "a": 1,
                    "b": 1
                },
                "id": 1
            }),
            json!({
                "jsonrpc": "2.0",
                "result": 2,
                "id": 1
            }),
        );
    }

    #[test]
    fn null_args() {
        let response = json!({
            "jsonrpc": "2.0",
            "result": "hello",
            "id": 1
        });
        assert_adder_response(
            json!({
                "jsonrpc": "2.0",
                "method": "greet",
                "params": {},
                "id": 1
            }),
            response.clone(),
        );
        assert_adder_response(
            json!({
                "jsonrpc": "2.0",
                "method": "greet",
                "params": [],
                "id": 1
            }),
            response.clone(),
        );
        assert_adder_response(
            json!({
                "jsonrpc": "2.0",
                "method": "greet",
                "params": null,
                "id": 1
            }),
            response.clone(),
        );
        assert_adder_response(
            json!({
                "jsonrpc": "2.0",
                "method": "greet",
                "id": 1
            }),
            response.clone(),
        );
    }

    #[test]
    fn null_return() {
        assert_adder_response(
            json!({
                "jsonrpc": "2.0",
                "method": "swallow",
                "params": [],
                "id": 1
            }),
            json!({
                "jsonrpc": "2.0",
                "result": null,
                "id": 1
            }),
        );
    }

    #[test]
    fn incorrect_method_name() {
        assert_eq!(
            error_code(json!({
                "jsonrpc": "2.0",
                "method": "nonexist",
                "params": [],
                "id": 1
            })),
            jsonrpc_core::ErrorCode::MethodNotFound,
        );
    }

    #[test]
    fn incorrect_args() {
        assert_eq!(
            error_code(json!({
                "jsonrpc": "2.0",
                "method": "wrapping_add",
                "params": [],
                "id": 1
            })),
            jsonrpc_core::ErrorCode::InvalidParams,
        );
        assert_eq!(
            error_code(json!({
                "jsonrpc": "2.0",
                "method": "wrapping_add",
                "params": {
                    "notanarg": 1,
                    "notarg": 1
                },
                "id": 1
            })),
            jsonrpc_core::ErrorCode::InvalidParams,
        );
        assert_eq!(
            error_code(json!({
                "jsonrpc": "2.0",
                "method": "wrapping_add",
                "params": [[], []],
                "id": 1
            })),
            jsonrpc_core::ErrorCode::InvalidParams,
        );
    }

    #[test]
    fn complex_type() {
        assert_adder_response(
            json!({
                "jsonrpc": "2.0",
                "method": "repeat_list",
                "params": [[1, 2, 3]],
                "id": 1
            }),
            json!({
                "jsonrpc": "2.0",
                "result": [1, 2, 3, 1, 2, 3],
                "id": 1
            }),
        );
        assert_eq!(
            error_code(json!({
                "jsonrpc": "2.0",
                "method": "repeat_list",
                "params": [[1], [12]],
                "id": 1
            }),),
            jsonrpc_core::ErrorCode::InvalidParams,
        );
        assert_adder_response(
            json!({
                "jsonrpc": "2.0",
                "method": "fail",
                "params": [],
                "id": 1
            }),
            json!({
                "jsonrpc": "2.0",
                "result": {
                    "Err": "tada!"
                },
                "id": 1
            }),
        );
        assert_adder_response(
            json!({
                "jsonrpc": "2.0",
                "method": "succeed",
                "params": [],
                "id": 1
            }),
            json!({
                "jsonrpc": "2.0",
                "result": {
                    "Ok": 1
                },
                "id": 1
            }),
        );
    }

    #[test]
    fn notification() {
        let request = json!({
            "jsonrpc": "2.0",
            "method": "succeed",
            "params": []
        });
        assert_eq!(
            (&AdderImpl {} as &dyn Adder).handle_request(request),
            MaybeReply::DontReply
        );
    }

    #[test]
    fn adder_client_non_macro() {
        #[easy_jsonrpc::rpc]
        trait Adder {
            fn checked_add(&self, a: usize, b: usize) -> Option<usize> {
                a.checked_add(b)
            }
        }

        #[allow(non_camel_case_types)]
        pub enum adder_client {}
        impl adder_client {
            fn checked_add(
                arg0: usize,
                arg1: usize,
            ) -> Result<
                easy_jsonrpc::BoundMethod<'static, Option<usize>>,
                easy_jsonrpc::ArgSerializeError,
            > {
                Ok(easy_jsonrpc::BoundMethod::new(
                    "checked_add",
                    vec![
                        serde_json::to_value(arg0).map_err(|_| easy_jsonrpc::ArgSerializeError)?,
                        serde_json::to_value(arg1).map_err(|_| easy_jsonrpc::ArgSerializeError)?,
                    ],
                ))
            }
        }

        impl Adder for () {}
        let handler = &() as &dyn Adder;

        let bind = adder_client::checked_add(1, 2).unwrap();
        let (call, tracker) = bind.call();
        let raw_response = handler
            .handle_request(call.as_request())
            .as_option()
            .unwrap();
        let mut response = easy_jsonrpc::Response::from_json_response(raw_response).unwrap();
        let result: Option<usize> = tracker.get_return(&mut response).unwrap();
        assert_eq!(result, Some(3));

        assert_eq!(
            handler.handle_request(
                adder_client::checked_add(1, 2)
                    .unwrap()
                    .notification()
                    .as_request()
            ),
            MaybeReply::DontReply
        );
    }

    #[test]
    fn adder_client_with_macro() {
        #[easy_jsonrpc::rpc]
        trait Adder {
            fn checked_add(&self, a: usize, b: usize) -> Option<usize> {
                a.checked_add(b)
            }
        }

        impl Adder for () {}
        let handler = &() as &dyn Adder;

        let bind = adder::checked_add(1, 2).unwrap();
        let (call, tracker) = bind.call();
        let raw_response = handler
            .handle_request(call.as_request())
            .as_option()
            .unwrap();
        let mut response = easy_jsonrpc::Response::from_json_response(raw_response).unwrap();
        let result: Option<usize> = tracker.get_return(&mut response).unwrap();
        assert_eq!(result, Some(3));

        let call = adder::checked_add(1, 2).unwrap();
        assert_eq!(
            handler.handle_request(call.notification().as_request()),
            MaybeReply::DontReply
        );
    }

    #[test]
    fn client_with_reference_args() {
        let handler = &AdderImpl {} as &dyn Adder;

        let bind = adder::echo_ref(&2).unwrap();
        let (call, tracker) = bind.call();
        let raw_response = handler
            .handle_request(call.as_request())
            .as_option()
            .unwrap();
        let mut response = easy_jsonrpc::Response::from_json_response(raw_response).unwrap();
        assert_eq!(tracker.get_return(&mut response).unwrap(), 2);

        let call = adder::echo_ref(&2).unwrap();
        assert_eq!(
            handler.handle_request(call.notification().as_request()),
            MaybeReply::DontReply
        );
    }

    #[test]
    fn response_double_get() {
        let handler = &AdderImpl as &dyn Adder;
        use easy_jsonrpc::Call;
        let bind0 = adder::checked_add(0, 0).unwrap();
        let (call0, tracker0) = bind0.call();
        let bind1 = adder::checked_add(1, 0).unwrap();
        let (call1, tracker1) = bind1.call();
        let bind2 = adder::wrapping_add(1, 1).unwrap();
        let (call2, tracker2) = bind2.call();
        let json_request = Call::batch_request(&[call0, call1, call2]);
        let json_response = handler.handle_request(json_request).as_option().unwrap();
        let mut response = easy_jsonrpc::Response::from_json_response(json_response).unwrap();
        assert_eq!(tracker0.get_return(&mut response).unwrap(), Some(0));
        assert_eq!(tracker2.get_return(&mut response).unwrap(), 2);

        // get_return removes the returned return value
        assert_eq!(tracker1.get_return(&mut response), Ok(Some(1)));
        assert_eq!(
            tracker1.get_return(&mut response),
            Err(easy_jsonrpc::ResponseFail::ResultNotFound)
        );
    }

    #[test]
    fn local_types() {
        #[derive(serde::Serialize, serde::Deserialize)]
        pub struct Foo;

        #[easy_jsonrpc::rpc]
        trait Bar {
            fn frob(&self) -> Foo;
            fn borf(&self, foo: Foo);
        }
    }
}
