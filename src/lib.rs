/*!
# Easy jsonrpc

Generates rpc handlers based on a trait definition.

```
use easy_jsonrpc::{self, JSONRPCServer};

// the jsonrpc_server generates a JSONRPCServer for &dyn Adder
#[easy_jsonrpc::jsonrpc_server]
pub trait Adder {
    fn checked_add(&self, a: isize, b: isize) -> Option<isize>;
    fn wrapping_add(&self, a: isize, b: isize) -> isize;
    fn is_some(&self, a: Option<usize>) -> bool;
    fn takes_ref(&self, rf: &isize);
}

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

// create an rpc handler
let adder = (&AdderImpl {} as &dyn Adder);

assert_eq!(
    adder.handle_raw(
        r#"{"jsonrpc": "2.0", "method": "wrapping_add", "params": [1, 2], "id": 1}"#
    ),
    Some(r#"{"jsonrpc":"2.0","result":3,"id":1}"#.into())
);

// Named arguments are handled automatically
assert_eq!(
    adder.handle_raw(
        r#"{"jsonrpc": "2.0", "method": "wrapping_add", "params": {"a": 1, "b": 2}, "id": 1}"#
    ),
    Some(r#"{"jsonrpc":"2.0","result":3,"id":1}"#.into())
);

// Calls with no id are treated as notifications
assert_eq!(
    adder.handle_raw(r#"{"jsonrpc": "2.0", "method": "wrapping_add", "params": [1, 1]}"#),
    None
);

// Calls with no return value return unit, aka `()` in rust, aka `null` in json
assert_eq!(
    adder.handle_raw(r#"{"jsonrpc": "2.0", "method": "takes_ref", "params": [1], "id": 1}"#),
    Some(r#"{"jsonrpc":"2.0","result":null,"id":1}"#.into())
);
```

Another example using handle_parsed instead of handle_raw.

```
use easy_jsonrpc::{self, JSONRPCServer};
use jsonrpc_core::types::{
    Call, Id, MethodCall, Params, Request, Response, Version, Output, Success,
};
use serde_json::json;

#[easy_jsonrpc::jsonrpc_server]
trait ExampleApi {
    fn frob(&self, thing: Vec<bool>) -> Vec<Vec<bool>>;
}

impl ExampleApi for () {
    fn frob(&self, thing: Vec<bool>) -> Vec<Vec<bool>> {
        eprintln!("Initiate frobbing.");
        vec![thing]
    }
}

let rpc_handler = (&() as &dyn ExampleApi);

let request = Request::Single(Call::MethodCall(MethodCall {
    jsonrpc: Some(Version::V2),
    method: "frob".into(),
    params: Params::Array(vec![json!([false, false, true])]),
    id: Id::Num(1),
}));

let response = Some(Response::Single(Output::Success(Success {
    jsonrpc: Some(Version::V2),
    result: json!([[false, false, true]]),
    id: Id::Num(1),
})));

assert_eq!(rpc_handler.handle_parsed(request), response);
```

Easy JSON RPC also generates typed client helpers.

```
use easy_jsonrpc::{self, JSONRPCServer};
use jsonrpc_core::types::*;

#[easy_jsonrpc::rpc]
trait Example {
    fn greet(&self, name: String) -> String;
}

impl Example for () {
    fn greet(&self, name: String) -> String {
        format!("Hello, {}!", name)
    }
}

let rpc_handler = &() as &dyn Example;

let (call, reciever) = example::greet::call("Shane".to_owned()).unwrap();
let request = Request::Single(Call::MethodCall(call));
let raw_request = serde_json::to_string(&request).unwrap();
let raw_response = rpc_handler.handle_raw(&raw_request).unwrap();
let response: Response = serde_json::from_str(&raw_response).unwrap();
let success = match response {
    Response::Single(Output::Success(s)) => s,
    _ => panic!(),
};
assert_eq!(&reciever.response(&success).unwrap(), "Hello, Shane!");
```
*/

pub use easy_jsonrpc_proc_macro::jsonrpc_server;
pub use easy_jsonrpc_proc_macro::rpc;

use serde::ser::Serialize;

// used from generated code
#[doc(hidden)]
pub use jsonrpc_core::types::{
    Call, Error, ErrorCode, Failure, Id, MethodCall, Notification, Output, Params, Request,
    Response, Success, Value, Version,
};
#[doc(hidden)]
pub use rand;
#[doc(hidden)]
pub use serde::de::Deserialize;
#[doc(hidden)]
pub use serde_json;

/// Handles jsonrpc calls.
pub trait JSONRPCServer {
    /// type-check params and call method if method exists
    fn handle(&self, method: &str, params: Params) -> Result<Value, Error>;

    /// extract method name and parameters from call
    /// if call is a normal method call, call `handle` and return result
    /// if call is a notification, call `handle` and return None
    /// if call is invalid return a jsonrpc failure
    fn handle_call(&self, call: Call) -> Option<Output> {
        match call {
            Call::Notification(Notification { method, params, .. }) => {
                let _ = self.handle(&method, params);
                None
            }
            Call::MethodCall(MethodCall {
                method,
                params,
                id,
                jsonrpc,
            }) => {
                let output = match self.handle(&method, params) {
                    Ok(ok) => Output::Success(Success {
                        jsonrpc,
                        result: ok,
                        id,
                    }),
                    Err(err) => Output::Failure(Failure {
                        jsonrpc,
                        error: err,
                        id,
                    }),
                };
                Some(output)
            }
            Call::Invalid { id } => Some(Output::Failure(Failure {
                jsonrpc: Some(Version::V2),
                error: Error::invalid_request(),
                id,
            })),
        }
    }

    /// Handle a structured jsonrpc request. If the request is a batch, handle the entire batch.
    /// return the singe result or a batch of results
    /// If the request consists of only notifications, return nothing as per jsonrpc 2.0 spec
    fn handle_parsed(&self, request: Request) -> Option<Response> {
        match request {
            Request::Single(call) => self.handle_call(call).map(Response::Single),
            Request::Batch(mut calls) => {
                let outputs = calls
                    .drain(..)
                    .filter_map(|call| self.handle_call(call))
                    .collect::<Vec<_>>();
                if outputs.is_empty() {
                    None
                } else {
                    Some(Response::Batch(outputs))
                }
            }
        }
    }

    /// Accept request as a jsonrpc formatted string. Call handler.
    /// Return result as a jsonrpc formatted string.
    fn handle_raw(&self, request: &str) -> Option<String> {
        let request: Request = serde_json::from_str(request)
            .unwrap_or(Request::Single(Call::Invalid { id: Id::Null }));
        self.handle_parsed(request).map(|response: Response| {
            // Here we assume that serializing a Response will not return an error.
            // we know the type of response, it doesn't contain mutexes or invalid utf strings so
            // serialization should succeed. If it does not, we respond with invalid json.
            serde_json::to_string(&response)
                .unwrap_or_else(|_| "unexpected serialization error, this is a bug".into())
        })
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
pub fn get_rpc_args(names: &[&'static str], params: Params) -> Result<Vec<Value>, InvalidArgs> {
    let ar: Vec<Value> = match params {
        Params::Array(ar) => ar,
        Params::Map(mut ma) => {
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
        Params::None => vec![],
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

/// used from generated code
#[doc(hidden)]
pub fn try_serialize<T: Serialize>(t: &T) -> Result<Value, Error> {
    // Serde serde_json::to_value does not perform io. It's still not safe to unwrap the result. For
    // example, the implementation of Serialize for Mutex returns an error if the mutex is poisined.
    // Another example, serialize(&std::Path) returns an error when it encounters invalid utf-8.
    serde_json::to_value(t).map_err(|e| Error {
        code: ErrorCode::ServerError(8),
        // serde::error::Error doesn't implement Serialize so we a human readable message instead of
        // a structured error.
        message: format!("Error serializing response. {}", e),
        data: None,
    })
}

/// Error returned when parsing a response on client side fail
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum ResponseFail {
    IdMismatch,
    InvalidResponse, // returned on serde::de failure
}

/// Thrown when arguments fail to be serialized. Possible causes include, but are not limited to:
/// - A poisoned mutex
/// - A cstring containing invalid utf-8
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct ArgSerializeError;

#[cfg(test)]
mod test {
    mod easy_jsonrpc {
        pub use crate::*;
    }
    use super::{jsonrpc_server, JSONRPCServer};
    use assert_matches::assert_matches;
    use jsonrpc_core::types::*;

    #[jsonrpc_server]
    pub trait Adder {
        fn checked_add(&self, a: isize, b: isize) -> Option<isize>;
        fn wrapping_add(&self, a: isize, b: isize) -> isize;
        fn greet(&self) -> String;
        fn swallow(&self);
        fn repeat_list(&self, lst: Vec<usize>) -> Vec<usize>;
        fn fail(&self) -> Result<isize, String>;
        fn succeed(&self) -> Result<isize, String>;
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
    }

    fn assert_adder_response(request: &str, response: &str) {
        assert_eq!(
            &(&AdderImpl {} as &dyn Adder).handle_raw(request).unwrap(),
            response
        );
    }

    fn handle_single(request: &str) -> Output {
        let a: Option<Response> =
            (&AdderImpl {} as &dyn Adder).handle_parsed(serde_json::from_str(&request).unwrap());
        match a {
            Some(Response::Single(a)) => a,
            _ => panic!(),
        }
    }

    #[test]
    fn positional_args() {
        assert_adder_response(
            r#"{"jsonrpc": "2.0", "method": "wrapping_add", "params": [1, 1], "id": 1}"#,
            r#"{"jsonrpc":"2.0","result":2,"id":1}"#,
        );
    }

    #[test]
    fn named_args() {
        assert_adder_response(
            r#"{"jsonrpc": "2.0", "method": "wrapping_add", "params": {"a": 1, "b":1}, "id": 1}"#,
            r#"{"jsonrpc":"2.0","result":2,"id":1}"#,
        );
    }

    #[test]
    fn null_args() {
        let response = r#"{"jsonrpc":"2.0","result":"hello","id":1}"#;
        assert_adder_response(
            r#"{"jsonrpc": "2.0", "method": "greet", "params": {}, "id": 1}"#,
            response,
        );
        assert_adder_response(
            r#"{"jsonrpc": "2.0", "method": "greet", "params": [], "id": 1}"#,
            response,
        );
        assert_adder_response(
            r#"{"jsonrpc": "2.0", "method": "greet", "params": null, "id": 1}"#,
            response,
        );
        assert_adder_response(
            r#"{"jsonrpc": "2.0", "method": "greet", "id": 1}"#,
            response,
        );
    }

    #[test]
    fn null_return() {
        assert_adder_response(
            r#"{"jsonrpc": "2.0", "method": "swallow", "params": [], "id": 1}"#,
            r#"{"jsonrpc":"2.0","result":null,"id":1}"#,
        );
    }

    #[test]
    fn incorrect_method_name() {
        assert_matches!(
            handle_single(r#"{"jsonrpc": "2.0", "method": "nonexist", "params": [], "id": 1}"#),
            Output::Failure(Failure {
                error:
                    Error {
                        code: ErrorCode::MethodNotFound,
                        ..
                    },
                ..
            })
        );
    }

    #[test]
    fn incorrect_args() {
        assert_matches!(
            handle_single(r#"{"jsonrpc": "2.0", "method": "wrapping_add", "params": [], "id": 1}"#),
            Output::Failure(Failure {
                error:
                    Error {
                        code: ErrorCode::InvalidParams,
                        ..
                    },
                ..
            })
        );
        assert_matches!(
            handle_single(
                r#"{"jsonrpc": "2.0", "method": "wrapping_add", "params": {
	                "notanarg": 1, "notarg": 1}, "id": 1}"#
            ),
            Output::Failure(Failure {
                error:
                    Error {
                        code: ErrorCode::InvalidParams,
                        ..
                    },
                ..
            })
        );
        assert_matches!(
            handle_single(
                r#"{"jsonrpc": "2.0", "method": "wrapping_add", "params": [[], []], "id": 1}"#
            ),
            Output::Failure(Failure {
                error:
                    Error {
                        code: ErrorCode::InvalidParams,
                        ..
                    },
                ..
            })
        );
    }

    #[test]
    fn complex_type() {
        assert_adder_response(
            r#"{"jsonrpc": "2.0", "method": "repeat_list", "params": [[1, 2, 3]], "id": 1}"#,
            r#"{"jsonrpc":"2.0","result":[1,2,3,1,2,3],"id":1}"#,
        );
        assert_matches!(
            handle_single(
                r#"{"jsonrpc": "2.0", "method": "repeat_list", "params": [[1], [12]], "id": 1}"#,
            ),
            Output::Failure(Failure {
                error:
                    Error {
                        code: ErrorCode::InvalidParams,
                        ..
                    },
                ..
            })
        );
        assert_adder_response(
            r#"{"jsonrpc": "2.0", "method": "fail", "params": [], "id": 1}"#,
            r#"{"jsonrpc":"2.0","result":{"Err":"tada!"},"id":1}"#,
        );
        assert_adder_response(
            r#"{"jsonrpc": "2.0", "method": "succeed", "params": [], "id": 1}"#,
            r#"{"jsonrpc":"2.0","result":{"Ok":1},"id":1}"#,
        );
    }

    #[test]
    fn notification() {
        let request =
            serde_json::from_str(r#"{"jsonrpc": "2.0", "method": "succeed", "params": []}"#)
                .unwrap();
        assert_eq!((&AdderImpl {} as &dyn Adder).handle_parsed(request), None);
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
                ) -> Result<(MethodCall, Self), ArgSerializeError> {
                    let id = rand::random::<u64>();
                    let mc = MethodCall {
                        jsonrpc: Some(Version::V2),
                        id: Id::Num(id),
                        method: "checked_add".to_owned(),
                        params: Params::Array(vec![
                            serde_json::to_value(arg0).map_err(|_| ArgSerializeError)?,
                            serde_json::to_value(arg1).map_err(|_| ArgSerializeError)?,
                        ]),
                    };
                    Ok((mc, Self { id }))
                }

                pub fn notification(
                    arg0: usize,
                    arg1: usize,
                ) -> Result<Notification, ArgSerializeError> {
                    Ok(Notification {
                        jsonrpc: Some(Version::V2),
                        method: "checked_add".to_owned(),
                        params: Params::Array(vec![
                            serde_json::to_value(arg0).map_err(|_| ArgSerializeError)?,
                            serde_json::to_value(arg1).map_err(|_| ArgSerializeError)?,
                        ]),
                    })
                }

                // make sure ids match, parse response
                pub fn response(&self, response: &Success) -> Result<Option<usize>, ResponseFail> {
                    if response.id != Id::Num(self.id) {
                        return Err(ResponseFail::IdMismatch);
                    }
                    <Option<usize>>::deserialize(&response.result)
                        .map_err(|_| ResponseFail::InvalidResponse)
                }
            }
        }

        impl Adder for () {}

        let handler = &() as &dyn Adder;

        let (method_call, tracker) = adder::checked_add::call(1, 2).unwrap();
        let output = handler.handle_call(Call::MethodCall(method_call)).unwrap();
        let success = match output {
            Output::Success(s) => s,
            Output::Failure(_) => panic!(),
        };
        let result: Option<usize> = tracker.response(&success).unwrap();
        assert_eq!(result, Some(3));

        let notification = adder::checked_add::notification(1, 2).unwrap();
        let output = handler.handle_call(Call::Notification(notification));
        assert_eq!(output, None);
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

        let (method_call, tracker) = adder::checked_add::call(1, 2).unwrap();
        let output = handler.handle_call(Call::MethodCall(method_call)).unwrap();
        let success = match output {
            Output::Success(s) => s,
            Output::Failure(_) => panic!(),
        };
        let result: Option<usize> = tracker.response(&success).unwrap();
        assert_eq!(result, Some(3));

        let notification = adder::checked_add::notification(1, 2).unwrap();
        let output = handler.handle_call(Call::Notification(notification));
        assert_eq!(output, None);
    }

    #[test]
    fn client_with_reference_args() {
        #[easy_jsonrpc::rpc]
        trait Adder {
            fn checked_add(&self, a: usize, b: &usize) -> Option<usize> {
                a.checked_add(*b)
            }
        }

        impl Adder for () {}

        let handler = &() as &dyn Adder;

        let (method_call, tracker) = adder::checked_add::call(1, &2).unwrap();
        let output = handler.handle_call(Call::MethodCall(method_call)).unwrap();
        let success = match output {
            Output::Success(s) => s,
            Output::Failure(_) => panic!(),
        };
        let result: Option<usize> = tracker.response(&success).unwrap();
        assert_eq!(result, Some(3));

        let notification = adder::checked_add::notification(1, &2).unwrap();
        let output = handler.handle_call(Call::Notification(notification));
        assert_eq!(output, None);
    }
}
