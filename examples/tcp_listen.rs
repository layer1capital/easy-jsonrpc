//! Tcp rpc server example

mod common;
use crate::common::create_frob_server;
use easy_jsonrpc::{Handler, MaybeReply};
use serde::Deserialize;
use serde_json;
use std::io::Read;
use std::net::TcpListener;
use std::time::Duration;

fn main() {
    let rpc_handler = create_frob_server();
    let listener = TcpListener::bind(("0.0.0.0", 4444)).unwrap();
    for stream in listener.incoming().filter_map(|connection| connection.ok()) {
        stream
            .set_read_timeout(Some(Duration::from_secs(1)))
            .expect("failed to set read timeout");
        stream
            .set_write_timeout(Some(Duration::from_secs(1)))
            .expect("failed to set write timeout");

        // parse json
        let mut reader = stream.take(64_000);
        let mut de = serde_json::Deserializer::from_reader(&mut reader);
        let value = match serde_json::Value::deserialize(&mut de) {
            Ok(value) => value,
            Err(_) => continue,
        };

        // call rpc
        let result = rpc_handler.handle_request(value);

        // return result
        let mut stream = reader.into_inner();
        match result {
            MaybeReply::Reply(value) => {
                let _ = serde_json::to_writer(&mut stream, &value);
            }
            MaybeReply::DontReply => {}
        }
    }
}
