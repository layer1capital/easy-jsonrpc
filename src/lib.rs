/*!
# Easy jsonrpc

Generates rpc handlers based on a trait definition.


```
// Defining an api

use easy_jsonrpc;

#[easy_jsonrpc::rpc]
pub trait Adder {
    fn checked_add(&self, a: isize, b: isize) -> Option<isize>;
    fn wrapping_add(&self, a: isize, b: isize) -> isize;
    fn is_some(&self, a: Option<usize>) -> bool;
    fn takes_ref(&self, rf: &isize);
}


// Server usage

// The macro call above generated a JSONRPCServer implementation for &dyn Adder, so if we write an
// an implementation of Adder, we can use it as a JSONRPCServer

use easy_jsonrpc::JSONRPCServer;
use serde_json::json;

struct AdderImpl;

impl Adder for AdderImpl {
    fn checked_add(&self, a: isize, b: isize) -> Option<isize> {
        a.checked_add(b)
    }
    fn wrapping_add(&self, a: isize, b: isize) -> isize {
        a.wrapping_add(b)
    }
    fn is_some(&self, a: Option<usize>) -> bool {
        a.is_some()
    }
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
    Some(json!({
        "jsonrpc": "2.0",
        "result": 3,
        "id": 1
    }))
);


// Client usage

let (call, tracker) = adder::checked_add::call(1, 2).unwrap();
let json_response = handler.handle_request(call.into_request()).unwrap();
let mut response = easy_jsonrpc::Response::from_raw(json_response).unwrap();
assert_eq!(tracker.get_return(&mut response).unwrap(), Some(3));


// Bonus bits

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
    Some(json!({
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
    None
);

// Batch calls are possible
use easy_jsonrpc::Call;
let (call0, tracker0) = adder::checked_add::call(0, 0).unwrap();
let (call1, tracker1) = adder::checked_add::call(1, 0).unwrap();
let (call2, tracker2) = adder::wrapping_add::call(1, 1).unwrap();
let json_request = Call::into_batch_request(&[call0, call1, call2]);
let json_response = handler.handle_request(json_request).unwrap();
let mut response = easy_jsonrpc::Response::from_raw(json_response).unwrap();
assert_eq!(tracker1.get_return(&mut response).unwrap(), Some(1));
assert_eq!(tracker0.get_return(&mut response).unwrap(), Some(0));
assert_eq!(tracker2.get_return(&mut response).unwrap(), 2);
```
*/

const SERIALZATION_ERROR: i64 = -32000;

pub use easy_jsonrpc_proc_macro::jsonrpc_server;
pub use easy_jsonrpc_proc_macro::rpc;

// used from generated code
#[doc(hidden)]
pub use jsonrpc_core::types::{
    self, Error, ErrorCode, Failure, Id, MethodCall, Notification, Output, Success, Version,
};
#[doc(hidden)]
pub use serde::de::Deserialize;
#[doc(hidden)]
pub use serde_json::{self, Value};

use rand;
use serde::ser::Serialize;
use serde_json::json;
use std::collections::BTreeMap;

/// Handles jsonrpc calls.
pub trait JSONRPCServer {
    /// type-check params and call method if method exists
    fn handle(&self, method: &str, params: Params) -> Result<Value, Error>;

    /// Parses raw_request as a jsonrpc request, handles request according to the jsonrpc spec.
    /// As per the spec, requests consisting of only notifications recieve no response. A lack of
    /// response is represented as Option::None. Any response which should be returned to the client
    /// is represented as Option::Some(value), where value can be directy serialized and sent as a
    /// response.
    fn handle_request(&self, raw_request: serde_json::Value) -> Option<Value> {
        let request: jsonrpc_core::Request = match serde_json::from_value(raw_request) {
            Ok(request) => request,
            Err(_) => {
                return Some(serde_json::json!({
                    "jsonrpc": "2.0",
                    "error": {
                        "code": -32700,
                        "message": "Parse error"
                    },
                    "id": null
                }));
            }
        };
        let response = handle_parsed_request(self, request)?;
        Some(serde_json::to_value(response).unwrap_or_else(|e| {
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

/// extract method name and parameters from call
/// if call is a normal method call, call `handle` and return result
/// if call is a notification, call `handle` and return None
/// if call is invalid return a jsonrpc failure
fn handle_call<S: ?Sized + JSONRPCServer>(slef: &S, call: jsonrpc_core::Call) -> Option<Output> {
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
fn handle_parsed_request<S: ?Sized + JSONRPCServer>(
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
#[derive(Debug)]
pub enum Params {
    Positional(Vec<Value>),
    Named(serde_json::Map<String, Value>),
}

impl Params {
    pub fn from_rc_params(params: jsonrpc_core::Params) -> Self {
        match params {
            jsonrpc_core::Params::Array(arr) => Params::Positional(arr),
            jsonrpc_core::Params::Map(map) => Params::Named(map),
            jsonrpc_core::Params::None => Params::Positional(vec![]),
        }
    }

    // Verify and convert jsonrpc Params into owned argument list.
    // Verifies:
    //    - Number of args in positional parameter list is correct
    //    - No missing args in named parameter object
    //    - No extra args in named parameter object
    // Absent parameter objects are interpreted as empty positional parameter lists
    //
    // this function needs to be public because it is used the code genterated by jsonrpc::server
    // the function is not a stable part of the api and should not be used by client crates
    #[doc(hidden)]
    pub fn get_rpc_args(self, names: &[&'static str]) -> Result<Vec<Value>, InvalidArgs> {
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
                    Some(key) => return Err(InvalidArgs::ExtraNamedParameter { name: key.clone() }),
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
/// A single rpc method call or notification with arguments.
#[derive(Debug)]
pub struct Call<'a> {
    method: &'a str,
    id: Option<u64>, // None indicates a notification
    args: Vec<Value>,
}

impl<'a> Call<'a> {
    /// Create a jsonrpc method call with a random id.
    /// Id is guaranteed not to be None when using this constructor.
    pub fn call(method: &'a str, args: Vec<Value>) -> Call {
        Self {
            method,
            id: Some(rand::random::<u64>()),
            args,
        }
    }

    /// Create a jsonrpc method call with no id. Jsonrpc servers do not respond to notifications.
    pub fn notification(method: &'a str, args: Vec<Value>) -> Call {
        Self {
            method,
            id: None,
            args,
        }
    }

    /// Convert call to a json object which can be serialized and sent to a jsonrpc server.
    pub fn into_request(&self) -> Value {
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
    pub fn into_batch_request(calls: &[Self]) -> Value {
        debug_assert!({
            fn contains_duplicates(list: &[u64]) -> bool {
                (1..list.len()).any(|i| list[i..].contains(&list[i - 1]))
            }
            let ids = calls.iter().filter_map(|call| call.id).collect::<Vec<_>>();
            !contains_duplicates(ids.as_slice())
        });
        Value::Array(calls.iter().map(Call::into_request).collect())
    }

    pub fn method(&self) -> &str {
        self.method
    }

    pub fn id(&self) -> Option<u64> {
        self.id
    }

    pub fn args(&self) -> &Vec<Value> {
        &self.args
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

/// Error returned when parsing a response on client side fail
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

#[derive(Clone, PartialEq, Debug)]
pub enum InvalidResponse {
    DeserailizeFailure,
    ContainsNonNumericKeys,
}

/// Special purpose structure for holding a group of responses. Allows for response lookup by id.
/// Does not support non-number ids.
pub struct Response {
    /// Mapping from id to return result of rpc call.
    pub outputs: BTreeMap<u64, Result<Value, Error>>,
}

impl Response {
    /// Deserialize response from jsonrpc server into a Response.
    /// Returns Err If:
    /// - response is not valid
    /// - response contains outputs with non-number ids
    pub fn from_raw(raw_jsonrpc_response: Value) -> Result<Self, InvalidResponse> {
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
                        Output::Success(Success { id: _, .. })
                        | Output::Failure(Failure { id: _, .. }) => {
                            Err(InvalidResponse::ContainsNonNumericKeys)
                        }
                    }
                },
            )
            .collect::<Result<BTreeMap<u64, Result<Value, Error>>, InvalidResponse>>()?;
        Ok(Self { outputs })
    }

    /// Attempt to retrieve output from response. If there is a match, remove and return it.
    pub fn remove(&mut self, id: u64) -> Option<Result<Value, Error>> {
        self.outputs.remove(&id)
    }
}

#[cfg(test)]
mod test {
    mod easy_jsonrpc {
        pub use crate::*;
    }
    use super::JSONRPCServer;
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
                .unwrap(),
            response
        );
    }

    fn error_code(request: Value) -> jsonrpc_core::ErrorCode {
        let raw_response = (&AdderImpl {} as &dyn Adder)
            .handle_request(request)
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
        assert_eq!((&AdderImpl {} as &dyn Adder).handle_request(request), None);
    }

    #[test]
    fn adder_client_non_macro() {
        #[easy_jsonrpc::jsonrpc_server]
        trait Adder {
            fn checked_add(&self, a: usize, b: usize) -> Option<usize> {
                a.checked_add(b)
            }
        }

        mod adder {
            use super::easy_jsonrpc::*;

            #[allow(non_camel_case_types)]
            pub struct checked_add {
                id: u64,
            }

            impl checked_add {
                // calls with random id
                pub fn call(
                    arg0: usize,
                    arg1: usize,
                ) -> Result<(Call<'static>, Self), ArgSerializeError> {
                    let id = rand::random::<u64>();
                    let mc = Call {
                        id: Some(id),
                        method: "checked_add",
                        args: vec![
                            serde_json::to_value(arg0).map_err(|_| ArgSerializeError)?,
                            serde_json::to_value(arg1).map_err(|_| ArgSerializeError)?,
                        ],
                    };
                    Ok((mc, Self { id }))
                }

                pub fn notification(
                    arg0: usize,
                    arg1: usize,
                ) -> Result<Call<'static>, ArgSerializeError> {
                    Ok(Call {
                        id: None,
                        method: "checked_add",
                        args: vec![
                            serde_json::to_value(arg0).map_err(|_| ArgSerializeError)?,
                            serde_json::to_value(arg1).map_err(|_| ArgSerializeError)?,
                        ],
                    })
                }

                /// Get typed return value from server response.
                /// If response contains the return value for this request, remove it from the
                /// server response, attempt to interpret the return value as a typed value.
                pub fn get_return(
                    &self,
                    response: &mut Response,
                ) -> Result<Option<usize>, ResponseFail> {
                    response
                        .remove(self.id)
                        .ok_or(ResponseFail::ResultNotFound)
                        .and_then(|result| result.map_err(ResponseFail::RpcError))
                        .and_then(|raw_return| {
                            <Option<usize>>::deserialize(&raw_return)
                                .map_err(|_| ResponseFail::InvalidResponse)
                        })
                }
            }
        }

        impl Adder for () {}
        let handler = &() as &dyn Adder;

        let (call, tracker) = adder::checked_add::call(1, 2).unwrap();
        let raw_response = handler.handle_request(call.into_request()).unwrap();
        let mut response = easy_jsonrpc::Response::from_raw(raw_response).unwrap();
        let result: Option<usize> = tracker.get_return(&mut response).unwrap();
        assert_eq!(result, Some(3));

        let call = adder::checked_add::notification(1, 2).unwrap();
        assert_eq!(handler.handle_request(call.into_request()), None);
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

        let (call, tracker) = adder::checked_add::call(1, 2).unwrap();
        let raw_response = handler.handle_request(call.into_request()).unwrap();
        let mut response = easy_jsonrpc::Response::from_raw(raw_response).unwrap();
        let result: Option<usize> = tracker.get_return(&mut response).unwrap();
        assert_eq!(result, Some(3));

        let call = adder::checked_add::notification(1, 2).unwrap();
        assert_eq!(handler.handle_request(call.into_request()), None);
    }

    #[test]
    fn client_with_reference_args() {
        let handler = &AdderImpl {} as &dyn Adder;

        let (call, tracker) = adder::echo_ref::call(&2).unwrap();
        let raw_response = handler.handle_request(call.into_request()).unwrap();
        let mut response = easy_jsonrpc::Response::from_raw(raw_response).unwrap();
        assert_eq!(tracker.get_return(&mut response).unwrap(), 2);

        let call = adder::echo_ref::notification(&2).unwrap();
        assert_eq!(handler.handle_request(call.into_request()), None);
    }

    #[test]
    fn response_double_get() {
        let handler = &AdderImpl as &dyn Adder;
        use easy_jsonrpc::Call;
        let (call0, tracker0) = adder::checked_add::call(0, 0).unwrap();
        let (call1, tracker1) = adder::checked_add::call(1, 0).unwrap();
        let (call2, tracker2) = adder::wrapping_add::call(1, 1).unwrap();
        let json_request = Call::into_batch_request(&[call0, call1, call2]);
        let json_response = handler.handle_request(json_request).unwrap();
        let mut response = easy_jsonrpc::Response::from_raw(json_response).unwrap();
        assert_eq!(tracker0.get_return(&mut response).unwrap(), Some(0));
        assert_eq!(tracker2.get_return(&mut response).unwrap(), 2);

        // get_return removes the returned return value
        assert_eq!(tracker1.get_return(&mut response), Ok(Some(1)));
        assert_eq!(
            tracker1.get_return(&mut response),
            Err(easy_jsonrpc::ResponseFail::ResultNotFound)
        );
    }
}
