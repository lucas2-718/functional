use crate::ctypes::Naming;
use crate::ctypes::Res;
use crate::ctypes::err_str;
use crate::ctypes::opt_err;
use crate::ctypes::unwrap_natural;
use crate::ctypes::ContainedTerm;
use crate::ctypes::Term::*;
use std::collections::HashMap;
use std::iter::once;
use std::time::Duration;

#[derive(Clone)]
struct DisplayContext {
    used: HashMap<String,usize>,
    names: Vec<String>,
}

fn subscriptify(mut s: usize) -> String {
    let mut digits = Vec::new();
    while (s>0) {
        let digit = s % 10;
        digits.push(digit);
        s /= 10;
    }
    digits.into_iter().rev().map(|v|{
        ['\u{2080}','\u{2081}','\u{2082}','\u{2083}','\u{2084}','\u{2085}','\u{2086}','\u{2087}','\u{2088}','\u{2089}'][v]
    }).collect()
}

impl DisplayContext {
    fn new() -> Self {
        Self {used: HashMap::new(), names: Vec::new()}
    }
    fn add_name(mut self,name: Naming) -> Self {
        let mut name = name.0;
        let v = self.used.entry(name.clone()).or_insert(0);
        name.push_str(&subscriptify(*v));
        self.names.push(name);
        *v+=1;
        self
    }
    fn last(&self) -> Option<&String> {
        self.names.last()
    }
    fn get(&self, n: usize) -> Res<&String> {
        opt_err(self.names.get(self.names.len()-1-n),"Index out of bounds!".to_string())
    }
}


#[derive(Clone,PartialEq, Eq, Hash, Debug)]
struct TypingContext {
    data: Vec<ContainedTerm>,
}

impl TypingContext {
    fn push(&mut self,v: ContainedTerm) -> Res<()> {
        self.push_scope()?;
        self.data.push(v.push_scope(0u8.into())?);
        Ok(())
        
    }
    fn push_scope(&mut self) -> Res<()> {
        let mut data = Vec::new();
        for item in self.data.drain(..) {
            data.push(item.push_scope(0u8.into())?);
        }
        self.data = data;
        Ok(())
    }
    #[track_caller]
    fn get(&self, n: usize) -> Res<&ContainedTerm> {
        if (n>=self.data.len()) {return err_str("Index out of bounds [positive]")}
        opt_err(self.data.get(self.data.len()-1-n),"Index out of bounds [negative??]".into())
    }
    fn new() -> Self {
        Self{data: Vec::new()}
    }
}

pub struct AliasMap(HashMap<ContainedTerm,String>);

impl AliasMap {
    pub fn new() -> Self {
        Self(HashMap::new())
    }
    pub fn add_alias(&mut self, term: ContainedTerm, name: String) {
        self.0.insert(term, name);
    }
    pub fn get(&self, term: &ContainedTerm) -> Option<&String> {
        self.0.get(term)
    }
}

pub fn pretty_print_base(t: ContainedTerm, aliases: &AliasMap) -> String {
    let mut output = String::new();
    let context = DisplayContext::new();
    pretty_print(t, context, TypingContext::new(), &mut output, aliases);
    output
}

#[must_use]
fn pretty_print(t: ContainedTerm, context: DisplayContext, mut tc: TypingContext, output: &mut String, aliases: &AliasMap) -> Res<()> {
    match aliases.get(&t) {
        None => (),
        Some(v) => {
            output.push_str(v);
            return Ok(())
        }
    }
    match t.pop() {
        DeBrujin(n, ty) => {
            let x = unwrap_natural(n);
            if tc.get(x)? != &ty {
                output.push_str("!(");
                pretty_print(ty, context.clone(), tc.clone(), output, aliases)?;
                output.push('/');
                pretty_print(tc.get(x)?.clone(), context.clone(), tc, output, aliases)?;
                output.push(')');
            }
            output.push_str(context.get(x).unwrap())
        },
        Lam(ty,body,name) => {
            let oc = context.clone();
            let context = context.add_name(name);
            let name = context.last().unwrap().clone();
            output.push('(');
            output.push_str(&name);
            output.push_str(": ");
            pretty_print(ty.clone(),oc,tc.clone(),output,aliases)?;
            output.push_str(" → ");
            tc.push(ty);
            pretty_print(body,context,tc,output,aliases)?;
            output.push(')');
        }
        Pi(ty,body,name) => {
            let oc = context.clone();
            let context = context.add_name(name);
            let name = context.last().unwrap().clone();
            output.push('(');
            output.push_str(&name);
            output.push_str(": ");
            pretty_print(ty.clone(),oc,tc.clone(),output,aliases)?;
            output.push_str(" → ");
            tc.push(ty);
            pretty_print(body,context,tc,output,aliases)?;
            output.push(')');
        }
        App(f,x) => {
            output.push('(');
            pretty_print(f,context.clone(),tc.clone(),output,aliases)?;
            output.push(' ');
            pretty_print(x, context, tc,output,aliases)?;
            output.push(')');
        }
        Universe(n) => {
            output.push_str(&format!("Type{{{}}}",n));
        }
        Nat => output.push('\u{2115}'),
        Zero => output.push('0'),
        Succ(x) => match x.clone().get_number() {
            None => {
                output.push_str("S ");
                pretty_print(x, context, tc,output, aliases)?;
            }
            Some(v) => output.push_str(&(v+1).to_string())
        }
        NatInd(v,u) => {
            output.push('(');
            output.push_str(&format!("Ind{{{}}} ",u));
            pretty_print(v,context,tc,output, aliases)?;
            output.push(')');
        }
        II => output.push('I'),
        IA => output.push_str("I\u{2080}"),
        IB => output.push_str("I\u{2081}"),
        Not(x) => {
            output.push('\u{AC}');
            pretty_print(x, context, tc, output, aliases)?;
        },
        And(x,y) => {
            output.push('(');
            pretty_print(x, context.clone(), tc.clone(), output, aliases)?;
            output.push('&');
            pretty_print(y,context,tc,output,aliases)?;
            output.push(')');
        }
        EqLam(f) => {
            output.push_str("EqLam");
            pretty_print(f,context,tc,output,aliases)?;
        }
        Eq(p,x,y) => {
            output.push('(');
            pretty_print(x, context.clone(), tc.clone(), output, aliases)?;
            output.push('\u{2261}');
            pretty_print(y,context.clone(),tc.clone(),output,aliases)?;
            if (p.clone().check_refl(IA.ctn().unwrap())?.is_none()) {
                output.push('?');
                pretty_print(p, context, tc, output, aliases)?;
            }
            output.push(')');
        }
        EqUw(p,i) => {
            pretty_print(p, context.clone(), tc.clone(), output, aliases)?;
            output.push('@');
            pretty_print(i, context, tc, output, aliases)?;
        }
        Transp(p,x) => {
            output.push_str("Transp(");
            pretty_print(p, context.clone(), tc.clone(), output, aliases)?;
            output.push_str(")(");
            pretty_print(x, context, tc, output, aliases)?;
            output.push(')');
        }
        Sig(x) => {
            output.push('\u{3A3}');
            pretty_print(x, context, tc, output, aliases)?;
        }
        Pair(_,a,b) => {
            output.push('(');
            pretty_print(a, context.clone(), tc.clone(), output, aliases)?;
            output.push(',');
            pretty_print(b, context, tc, output, aliases)?;
            output.push(')');
        }
        SigInd(x,n) => {
            output.push_str(&format!("Ind\u{3A3}{{{}}} ",n));
            pretty_print(x, context, tc, output, aliases)?;
        }
        v => panic!("Unimplemented: {:?}",v),
    };
    Ok(())
}