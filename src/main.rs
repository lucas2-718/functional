use functional::{bool, ctypes::{Term::*, num}, display::{AliasMap, pretty_print_base}, equals::refl, numbers::{NatData}, *};


fn run() {
    let mut aliasmap = AliasMap::new();
    aliasmap.add_alias(refl(ctypes::Term::Zero.ctn().unwrap()).unwrap(), "reflzero".into());
    //equals::Theorems::new(0u8.into(),0u8.into()).unwrap();
    //bool::BoolData::new().unwrap();
    //println!("{}",pretty_print_base(zero_eq_trivial().unwrap().typed().unwrap(),&aliasmap));
    let booldata = bool::BoolData::new().unwrap();
    let bfalse = booldata.bool_false.clone();
    let btrue = booldata.bool_true.clone();
    aliasmap.add_alias(btrue.clone(), "true".into());
    aliasmap.add_alias(bfalse.clone(), "false".into());
    let bool_ind = booldata.generic_bool_ind(0u8.into()).unwrap();
    //println!("{}",pretty_print_base(bool_ind, &aliasmap));

    let natdata = NatData::new().unwrap();
    println!("{:?}",App(App(natdata.add_func,num(15)).ctn().unwrap(),num(17)).ctn().unwrap().get_number());

    //let fs = impossible::False::new().unwrap();
    //let exfs = fs.clone().exfalso(ctypes::Term::II.ctn().unwrap()).unwrap();
    //println!("{}",pretty_print_base(exfs, &AliasMap::new()))
}

fn main(){
    std::thread::Builder::new().stack_size(1024*1024*64).name("run".to_string()).spawn(run).unwrap().join().unwrap(); // 64 MB of stack should be sufficient :3
}