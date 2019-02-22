[![Build Status](https://travis-ci.org/layer1capital/easy-jsonrpc.svg?branch=master)](https://travis-ci.org/layer1capital/easy-jsonrpc)

# Easy JSON RPC

Generate a jsonrpc handler from a trait definition.

```rust
use easy_jsonrpc::{self, JSONRPCServer};

#[easy_jsonrpc::jsonrpc_server]
pub trait Adder {
    fn checked_add(&self, a: isize, b: isize) -> Option<isize>;
}

struct AdderImpl;

impl Adder for AdderImpl {
    fn checked_add(&self, a: isize, b: isize) -> Option<isize> {
        a.checked_add(b)
    }
}

fn main() {
    let adder = (&AdderImpl {} as &dyn Adder);

    assert_eq!(
        adder.handle_raw(
            r#"{"jsonrpc": "2.0", "method": "wrapping_add", "params": [1, 2], "id": 1}"#
        ).unwrap(),
        r#"{"jsonrpc":"2.0","result":3,"id":1}"#.into()
    );
}
```

Client generator not yet implemented.
