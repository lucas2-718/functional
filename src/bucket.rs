// Motivation for this file -- lambdas essentially act as buckets that can overfill

use std::{cell::RefCell, collections::HashSet, fmt::{Debug, Display}, hash::Hash, panic::Location, rc::Rc};

use crate::unique::{Cache, GlobalMap, Unique};


#[derive(Hash,Eq,PartialEq,Ord,PartialOrd,Clone,Copy)]
pub struct Natural(usize);

impl Display for Natural {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.0,f)
    }
}

impl Debug for Natural {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.0,f)
    }
}

impl Natural {
    pub fn pred(self) -> Self {
        Self(self.0.checked_sub(1).unwrap())
    }
    pub fn suc(self) -> Self {
        Self(self.0.checked_add(1).unwrap())
    }
    pub fn add(self,other: Self) -> Self {
        Self(self.0.checked_add(other.0).unwrap())
    }
    pub fn sub(self,other: Self) -> Result<Self,Self> {
        if (self.0>=other.0) {
            Ok(Self(self.0-other.0))
        }
        else {
            Err(Self(other.0-self.0))
        }
    }
}

impl From<u8> for Natural {
    fn from(value: u8) -> Self {
        Self(value.into())
    }
}

#[derive(Clone,Eq,PartialEq)]
pub struct ErrorType {
    message: String,
    stacktrace: Vec<&'static Location<'static>>,
}

impl ErrorType {
    fn new(msg: String) -> Self {
        ErrorType {message:msg, stacktrace: Vec::new()}
    }
}

impl Display for ErrorType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f,"Error: {}\n",self.message)?;
        Ok(for i in 0..self.stacktrace.len() {
            write!(f,"    -> {}\n",self.stacktrace[i])?
        })
    }
}

impl Debug for ErrorType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

pub type Res<T> = Result<T,ErrorType>;

pub trait Blame {
    #[track_caller]
    fn blame(self) -> Self;
}

impl<T> Blame for Res<T> {
    #[track_caller]
    fn blame(self) -> Self {
        match self {
            Ok(v) => Ok(v),
            Err(mut e) => Err({
                e.stacktrace.push(Location::caller());
                e
            })
        }
    }
}

#[track_caller]
pub fn opt_err<T>(x: Option<T>, msg: String) -> Res<T> {
    match x {
        Some(v) => Ok(v),
        None => Err(ErrorType{message:msg,stacktrace:Vec::new()}).blame()
    }
}


#[derive(Clone,Debug)]
pub struct Naming(pub String);
impl From<String> for Naming {
    fn from(value: String) -> Self {
        Self(value)
    }
}
impl From<&str> for Naming {
    fn from(value: &str) -> Self {
        Self(value.into())
    }
}

impl Naming {
    fn new(s: &str) -> Self {
        Self(s.to_string())
    }
}
impl PartialEq for Naming {
    fn eq(&self, other: &Self) -> bool {
        true
    }
    fn ne(&self, other: &Self) -> bool {
        false
    }
}
impl std::cmp::Eq for Naming {}
impl Hash for Naming {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        
    }
}

thread_local! {static SM: RefCell<HashSet<Rc<(Term,Cache<TermCache>)>>> = RefCell::new(HashSet::new());}

#[derive(Hash,Eq,PartialEq,Clone,PartialOrd, Ord)]
struct GM;
impl GlobalMap<(Term,Cache<TermCache>)> for GM {
    fn insert(&self, value: Rc<(Term,Cache<TermCache>)>) -> Rc<(Term,Cache<TermCache>)> {
        SM.with(|v|{
            let mut v = v.borrow_mut();
            v.insert(value.clone());
            v.get(&value).unwrap().clone()
        })
    }
    fn remove(&self, value: Rc<(Term,Cache<TermCache>)>) {
        SM.with(|v|{v.borrow_mut().remove(&value);})
    }
}

#[track_caller]
pub fn unwrap_natural(n: Natural) -> usize {
    n.0
}

#[derive(Clone,PartialEq, Eq, Hash,PartialOrd, Ord, Debug)]
pub struct ContainedTerm(Unique<GM,(Term,Cache<TermCache>)>);

#[derive(Clone,Debug)]
pub struct TermCache {
    peak: Natural, // how far does the term go upwards (i.e. how many variables are unquantified)
}

#[derive(Clone,PartialEq, Eq, Debug, Hash)]
pub enum Term {
    DeBrujin {
        ty: ContainedTerm,
    },
    Lambda {
        argty: ContainedTerm,
        argn: Naming,
        body: ContainedTerm,
    },
    App {
        func: ContainedTerm,
        param: ContainedTerm,
    },
    Push {
        layers: Natural,
        value: ContainedTerm
    },
    Pop { // every pop has traverse 1
        height: Natural,
        value: ContainedTerm,
    }
}