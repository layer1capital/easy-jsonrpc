//! Http rpc server example

mod common;
use crate::common::create_frob_server;
use easy_jsonrpc::{Handler, MaybeReply};
use serde_json::{self, json};
use std::net::{Ipv6Addr, SocketAddrV6};
use std::sync::Arc;
use warp::filters::body::content_length_limit;
use warp::post2;
use warp::Filter;
use warp::Reply;

fn main() {
    let addr = SocketAddrV6::new(Ipv6Addr::UNSPECIFIED, 4444, 0, 0);

    let rpc_handler = Arc::new(create_frob_server());

    let responder = post2()
        .and(content_length_limit(1024 * 32))
        .and(warp::body::json::<serde_json::Value>())
        .map(move |request| {
            let response: MaybeReply = rpc_handler.handle_request(request);
            let reply = match response {
                MaybeReply::Reply(json_val) => json_val,
                MaybeReply::DontReply => json!(null),
            };
            to_warp_result(reply)
        });

    warp::serve(responder).run(addr);
}

fn to_warp_result(json_value: serde_json::Value) -> impl Reply {
    Ok(warp::reply::json(&json_value))
}
