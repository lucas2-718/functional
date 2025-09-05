#![allow(unused,non_snake_case)]

use crate::ctypes::Res;
mod unique;
//mod dtypes;
mod ctypes;
//mod parse;
mod display;
mod numbers;
mod equals;


fn run() {
    equals::run(0u8.into()).unwrap();
}

fn main(){
    std::thread::Builder::new().stack_size(1024*1024*64).name("run".to_string()).spawn(run).unwrap().join().unwrap(); // 64 MB of stack should be sufficient :3
}