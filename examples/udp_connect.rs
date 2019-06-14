//! sends requests to the server defined in udp_listener

#[allow(dead_code)]
mod common;

use common::frob_machine; // client helpers generated automatically
use easy_jsonrpc::ArgSerializeError;
use easy_jsonrpc::BoundMethod;
use easy_jsonrpc::Response;
use serde::Deserialize;
use std::convert::TryInto;
use std::io;
use std::io::Cursor;
use std::net::Ipv6Addr;
use std::net::SocketAddr;
use std::net::SocketAddrV6;
use std::net::UdpSocket;
use std::time::Duration;

const MAX_IPV4_UDP_DATASIZE: usize = 65_527;

fn main() {
    let client = FrobClient::new(SocketAddrV6::new(Ipv6Addr::LOCALHOST, 4444, 0, 0));

    client.call(frob_machine::frob()).unwrap();
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

fn call_over_udp<R: Deserialize<'static>>(
    address: &SocketAddrV6,
    method: &BoundMethod<'_, R>,
) -> io::Result<R> {
    let socket = UdpSocket::bind(SocketAddr::from((Ipv6Addr::UNSPECIFIED, 0)))?;
    socket.connect(address)?;
    let (request, tracker) = method.call();
    let mut send_buf = [0u8; MAX_IPV4_UDP_DATASIZE];
    let len = serialize_for_udp(&request.as_request(), &mut send_buf)?;
    socket.send(&send_buf[..len])?;
    let mut recv_buf = send_buf;
    socket
        .set_read_timeout(Some(Duration::from_millis(500)))
        .expect("could not set read timeout on socket");
    let len = socket.recv(&mut recv_buf)?;
    let value = serde_json::from_slice(&recv_buf[..len])?;
    let mut response = Response::from_json_response(value)
        .map_err(|_| io::Error::from(io::ErrorKind::InvalidData))?;
    tracker
        .get_return(&mut response)
        .map_err(|_| io::Error::from(io::ErrorKind::InvalidData))
}

fn serialize_for_udp(
    value: &serde_json::Value,
    send_buf: &mut [u8; MAX_IPV4_UDP_DATASIZE],
) -> Result<usize, serde_json::error::Error> {
    let mut send = Cursor::new(&mut send_buf[..]);
    serde_json::to_writer(&mut send, value)?;
    Ok(send
        .position()
        .try_into()
        .expect("could not convert u64 with expected max value MAX_IPV4_UDP_DATASIZE to usize"))
}

struct FrobClient {
    address: SocketAddrV6,
}

impl FrobClient {
    fn new(address: SocketAddrV6) -> FrobClient {
        FrobClient { address }
    }

    fn call<R: Deserialize<'static>>(
        &self,
        method: Result<BoundMethod<'_, R>, ArgSerializeError>,
    ) -> io::Result<R> {
        call_over_udp(
            &self.address,
            &method.map_err(|_e| io::Error::from(io::ErrorKind::InvalidInput))?,
        )
    }
}
