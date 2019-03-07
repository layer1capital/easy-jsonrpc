[![Build Status](https://travis-ci.org/layer1capital/easy-jsonrpc.svg?branch=master)](https://travis-ci.org/layer1capital/easy-jsonrpc)

# Easy JSON RPC

Generate a jsonrpc handler and client helpers from a trait definition. [docs](https://docs.rs/easy-jsonrpc)

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
use easy_jsonrpc::Handler;
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
    Some(json!({
        "jsonrpc": "2.0",
        "result": 3,
        "id": 1
    }))
);
```

## Client side usage

```rust
let bind = adder::checked_add(1, 2).unwrap();
let (call, tracker) = bind.call();
let json_response = handler.handle_request(call.as_request()).unwrap();
let mut response = easy_jsonrpc::Response::from_json_response(json_response).unwrap();
assert_eq!(tracker.get_return(&mut response).unwrap(), Some(3));
```

## Bonus bits

Named arguments are handled for free.

```rust
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
```

Notifications (calls without an id) are handled sanely.

```rust
assert_eq!(
    handler.handle_request(json!({
        "jsonrpc": "2.0",
        "method": "wrapping_add",
        "params": [1, 1]
    })),
    None
);
```

Batch calls are possible

```rust
use easy_jsonrpc::Call;
let bind0 = adder::checked_add(0, 0).unwrap();
let (call0, tracker0) = bind0.call();
let bind1 = adder::checked_add(1, 0).unwrap();
let (call1, tracker1) = bind1.call();
let bind2 = adder::wrapping_add(1, 1).unwrap();
let (call2, tracker2) = bind2.call();
let json_request = Call::batch_request(&[call0, call1, call2]);
let json_response = handler.handle_request(json_request).unwrap();
let mut response = easy_jsonrpc::Response::from_json_response(json_response).unwrap();
assert_eq!(tracker1.get_return(&mut response).unwrap(), Some(1));
assert_eq!(tracker0.get_return(&mut response).unwrap(), Some(0));
assert_eq!(tracker2.get_return(&mut response).unwrap(), 2);
```
