//! Udp rpc server example

mod common;
use crate::common::create_frob_server;
use easy_jsonrpc::{Handler, MaybeReply};
use serde_json;
use std::convert::TryInto;
use std::io::Cursor;
use std::net::Ipv6Addr;
use std::net::SocketAddrV6;
use std::net::UdpSocket;

const MAX_IPV4_UDP_DATASIZE: usize = 65_527;

fn main() {
    let rpc_handler = create_frob_server();
    let socket = UdpSocket::bind(SocketAddrV6::new(Ipv6Addr::UNSPECIFIED, 4444, 0, 0)).unwrap();
    let mut recv_buf = [0u8; MAX_IPV4_UDP_DATASIZE];
    loop {
        let (len, src) = match socket.recv_from(&mut recv_buf) {
            Ok(lensrc) => lensrc,
            Err(err) => {
                eprintln!("{}", err);
                break;
            }
        };

        // parse json
        let value = match serde_json::from_slice(&recv_buf[..len]) {
            Ok(value) => value,
            Err(_) => {
                eprintln!("got invalid json");
                continue;
            }
        };

        // call rpc
        let result = rpc_handler.handle_request(value);

        // check if reply is needed
        let value = match result {
            MaybeReply::Reply(value) => value,
            MaybeReply::DontReply => {
                continue;
            }
        };

        // serialize response
        let mut send_buf = [0u8; MAX_IPV4_UDP_DATASIZE];
        let mut send = Cursor::new(&mut send_buf[..]);
        if serde_json::to_writer(&mut send, &value).is_err() {
            eprintln!("failed to serialize json");
            continue;
        }
        let len = send
            .position()
            .try_into()
            .expect("could not convert u64 with expected max value MAX_IPV4_UDP_DATASIZE to usize");

        // send response
        let _ = socket.send_to(&send.get_ref()[..len], src);
    }
}
