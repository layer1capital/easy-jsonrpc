//! sends requests to the server defined in tcp_server

#[allow(dead_code)]
mod common;

use common::frob_machine; // client helpers generated automatically
use easy_jsonrpc::ArgSerializeError;
use easy_jsonrpc::BoundMethod;
use easy_jsonrpc::Response;
use serde::Deserialize;
use std::io;
use std::io::{Read, Write};
use std::net::SocketAddr;
use std::net::TcpStream;
use std::time::Duration;

fn main() {
    // manual example
    manual_frob();

    // using a helper function
    call_over_tcp(
        &([127, 0, 0, 1], 4444).into(),
        &frob_machine::frob().unwrap(),
    )
    .unwrap();

    // abstracting even more
    let client = FrobClient::new(([127, 0, 0, 1], 4444).into());

    client.call(frob_machine::frob()).unwrap();
    client.call(frob_machine::unfrob()).unwrap();
    let frob_count: i32 = client.call(frob_machine::get_frob_count()).unwrap();
    dbg!(frob_count);
    client
        .call(frob_machine::ultimate_frob(vec![
            1, 2, 4, 8, -8, -4, -2, -1,
        ]))
        .unwrap();
}

/// calls the frob rpc without using helper functions
fn manual_frob() {
    let mut stream =
        TcpStream::connect_timeout(&([127, 0, 0, 1], 4444).into(), Duration::from_millis(500))
            .expect("failed to connect");
    let bound_method = frob_machine::frob().expect("failed to serialize empty argument list");
    let (request, tracker) = bound_method.call();
    serde_json::to_writer(&mut stream, &request.as_request()).expect("failed to write to stream");
    // doesn't put a cap on the size of the response
    let json = serde_json::from_reader(&mut stream).expect("failed to read json from stream");
    let mut response = Response::from_json_response(json).expect("server gave an invalid response");
    tracker
        .get_return(&mut response)
        .expect("server did not respond to rpc");
}

fn call_stream<S: Read + Write, R: Deserialize<'static>>(
    stream: &mut S,
    method: &BoundMethod<'_, R>,
) -> io::Result<R> {
    let (request, tracker) = method.call();
    serde_json::to_writer(&mut *stream, &request.as_request()).expect("failed to write to stream");
    let response = serde_json::from_reader(stream)?;
    let mut response = Response::from_json_response(response)
        .map_err(|_e| io::Error::from(io::ErrorKind::InvalidData))?;
    tracker
        .get_return(&mut response)
        .map_err(|_e| io::Error::from(io::ErrorKind::InvalidData))
}

fn call_over_tcp<R: Deserialize<'static>>(
    address: &SocketAddr,
    method: &BoundMethod<'_, R>,
) -> io::Result<R> {
    let mut stream = TcpStream::connect_timeout(address, Duration::from_millis(500))?;
    call_stream(&mut stream, method)
}

struct FrobClient {
    address: SocketAddr,
}

impl FrobClient {
    fn new(address: SocketAddr) -> FrobClient {
        FrobClient { address }
    }

    fn call<R: Deserialize<'static>>(
        &self,
        method: Result<BoundMethod<'_, R>, ArgSerializeError>,
    ) -> io::Result<R> {
        call_over_tcp(
            &self.address,
            &method.map_err(|_e| io::Error::from(io::ErrorKind::InvalidInput))?,
        )
    }
}
