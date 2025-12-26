use functional::{bool, display::{AliasMap, pretty_print_base}, equals::refl, numbers::zero_eq_trivial, *};


fn run() {
    let mut aliasmap = AliasMap::new();
    aliasmap.add_alias(refl(ctypes::Term::Zero.ctn().unwrap()).unwrap(), "reflzero".into());
    //equals::Theorems::new(0u8.into(),0u8.into()).unwrap();
    //bool::BoolData::new().unwrap();
    //println!("{}",pretty_print_base(zero_eq_trivial().unwrap().typed().unwrap(),&aliasmap));
    let booldata = bool::BoolData::new().unwrap();
    let bfalse = booldata.bool_false.clone();
    let bool_ind = booldata.bool_ind(bfalse, 0u8.into()).unwrap();
    println!("{}",pretty_print_base(bool_ind, &aliasmap));

    //let fs = impossible::False::new().unwrap();
    //let exfs = fs.clone().exfalso(ctypes::Term::II.ctn().unwrap()).unwrap();
    //println!("{}",pretty_print_base(exfs, &AliasMap::new()))
}

fn main(){
    std::thread::Builder::new().stack_size(1024*1024*64).name("run".to_string()).spawn(run).unwrap().join().unwrap(); // 64 MB of stack should be sufficient :3
}