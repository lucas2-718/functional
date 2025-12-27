use std::io::stdin;

use functional::{bool, ctypes::{Term::*, num}, display::{AliasMap, pretty_print_base}, equals::refl, numbers::{NatData}, *};


fn run() {
    let mut aliasmap = AliasMap::new();
    aliasmap.add_alias(refl(ctypes::Term::Zero.ctn().unwrap()).unwrap(), "reflzero".into());
    let booldata = bool::BoolData::new().unwrap();
    let natdata = NatData::new().unwrap();
    
    println!("raw definition of boolean type : {}", pretty_print_base(booldata.bool_type.get(), &aliasmap));

    aliasmap.add_alias(booldata.bool_true.get(), "true".into());
    aliasmap.add_alias(booldata.bool_false.get(), "false".into());
    aliasmap.add_alias(booldata.bool_type.get(), "bool".into());
    aliasmap.add_alias(booldata.trim.get(),"booltrim".into());
    let bool_ind = booldata.generic_bool_ind(0u8.into()).unwrap();
    
    println!("boolean induction principle type : {}",pretty_print_base(bool_ind.get().typed().unwrap(), &aliasmap));

    println!("addition definition : {:?}",natdata.add_func);

    
    let fs = impossible::FalseData::new().unwrap();
    let exfs = fs.clone().exfalso(ctypes::Term::II.ctn().unwrap()).unwrap();
    println!("example exfalso into the II type, which is inhabited, but this is done through exfalso {}",pretty_print_base(exfs, &AliasMap::new()));

    println!("Input two numbers line-separated to be added via the inductively defined add function (unary representation means numbers > 100 can take a while though!)");

    let mut x = String::new();
    let mut y = String::new();
    stdin().read_line(&mut x).unwrap();
    stdin().read_line(&mut y).unwrap();

    let x : usize = x.chars().filter(|c|{c.is_numeric()}).collect::<String>().parse().unwrap();
    let y : usize = y.chars().filter(|c|{c.is_numeric()}).collect::<String>().parse().unwrap();

    println!("added terms result : {}",App(App(natdata.add_func.get(),num(x)).ctn().unwrap(),num(y)).ctn().unwrap().get_number().unwrap());


}

fn main(){
    std::thread::Builder::new().stack_size(1024*1024*64).name("run".to_string()).spawn(run).unwrap().join().unwrap(); // 64 MB of stack should be sufficient :3
}