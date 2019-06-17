//! sends requests to the server defined in http_listener

#[allow(dead_code)]
mod common;

use common::frob_machine; // client helpers generated automatically
use easy_jsonrpc::{BoundMethod, Response};
use reqwest::Client;
use serde::Deserialize;
use serde_json::json;
use serde_json::Value;
use std::net::{Ipv6Addr, SocketAddrV6};

fn main() {
    let server_addr = SocketAddrV6::new(Ipv6Addr::LOCALHOST, 4444, 0, 0);
    let ret = post(&server_addr, &json!([])).unwrap();
    assert_eq!(ret, Value::Null);

    rpc(&server_addr, &frob_machine::frob().unwrap()).unwrap();
    rpc(&server_addr, &frob_machine::frob().unwrap()).unwrap();
    rpc(&server_addr, &frob_machine::unfrob().unwrap()).unwrap();
    rpc(
        &server_addr,
        &frob_machine::ultimate_frob(vec![1, 2, 4, 8, -8, -4, -2, -1, -800]).unwrap(),
    )
    .unwrap();
    let frob_count: i32 = rpc(&server_addr, &frob_machine::get_frob_count().unwrap()).unwrap();
    dbg!(frob_count);
}

fn rpc<R: Deserialize<'static>>(
    addr: &SocketAddrV6,
    method: &BoundMethod<'_, R>,
) -> Result<R, RpcErr> {
    let (request, tracker) = method.call();
    let json_response = post(addr, &request.as_request())?;
    let mut response = Response::from_json_response(json_response)?;
    Ok(tracker.get_return(&mut response)?)
}

fn post(addr: &SocketAddrV6, body: &Value) -> Result<Value, reqwest::Error> {
    let client = Client::new();
    client
        .post(&format!("http://{}", addr))
        .json(body)
        .send()?
        .error_for_status()?
        .json()
}

#[derive(Debug)]
enum RpcErr {
    Http(reqwest::Error),
    InvalidResponse,
}

impl From<easy_jsonrpc::InvalidResponse> for RpcErr {
    fn from(_other: easy_jsonrpc::InvalidResponse) -> Self {
        RpcErr::InvalidResponse
    }
}

impl From<easy_jsonrpc::ResponseFail> for RpcErr {
    fn from(_other: easy_jsonrpc::ResponseFail) -> Self {
        RpcErr::InvalidResponse
    }
}

impl From<reqwest::Error> for RpcErr {
    fn from(other: reqwest::Error) -> Self {
        RpcErr::Http(other)
    }
}
