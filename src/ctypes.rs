use std::{array, cell::RefCell, cmp::Ordering, collections::HashSet, fmt::{Debug, Display}, hash::Hash, panic::Location, rc::Rc};

use memoize::memoize;
use crate::unique::{Unique,GlobalMap};

/// A wrapper on usize that ensures that there is no silent wrapping occuring
/// 
/// Simulates a natural number, and panics if it gets too big (which will probably never happen)
/// ```
/// let number : Natural = 0u8.into()
/// let number = number.suc().suc().pred();
/// assert_eq!(number,Natural::from(1u8.into()));
/// ```
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
    /// Returns the Natural before this one, or panics
    pub fn pred(self) -> Self {
        Self(self.0.checked_sub(1).unwrap())
    }
    /// Returns the Natural after this one, and panics on overflow
    pub fn suc(self) -> Self {
        Self(self.0.checked_add(1).unwrap())
    }
}

impl From<u8> for Natural {
    fn from(value: u8) -> Self {
        Self(value.into())
    }
}

/// An error struct that can record a stack trace of where it has been
#[derive(Clone,Eq,PartialEq)]
pub struct ErrorType {
    message: String,
    stacktrace: Vec<&'static Location<'static>>,
}

impl ErrorType {
    /// Create a new error with a message and an empty stack trace
    pub fn new(msg: String) -> Self {
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

/// A result with a string error message and a stack trace
pub type Res<T> = Result<T,ErrorType>;

/// The Blame trait indicates an ability to add context to an error
pub trait Blame {
    /// The blame function adds context to an error, usually using the location of the caller
    #[track_caller]
    fn blame(self) -> Self;
}

impl<T> Blame for Res<T> {
    /// The blame function adds one location to the stack trace.
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

/// convert an option to an error type with a message
#[track_caller]
pub fn opt_err<T>(x: Option<T>, msg: String) -> Res<T> {
    match x {
        Some(v) => Ok(v),
        None => Err(ErrorType{message:msg,stacktrace:Vec::new()}).blame()
    }
}

/// The struct Naming wraps a string and is just a name for a variable
/// However, all namings are equal and do not affect hashing
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
    /// Creates a new naming from a str, wrapping its String value
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

thread_local! {static SM: RefCell<HashSet<Rc<Term>>> = RefCell::new(HashSet::new());}

/// Unwraps a natural into its corresponding usize, usually for debug purposes
#[track_caller]
pub fn unwrap_natural(n: Natural) -> usize {
    n.0
}

#[derive(Hash,Eq,PartialEq,Clone,PartialOrd, Ord)]
struct GM;
impl GlobalMap<Term> for GM {
    fn insert(&self, value: Rc<Term>) -> Rc<Term> {
        SM.with(|v|{
            let mut v = v.borrow_mut();
            v.insert(value.clone());
            v.get(&value).unwrap().clone()
        })
    }
    fn remove(&self, value: Rc<Term>) {
        SM.with(|v|{v.borrow_mut().remove(&value);})
    }
}

/// An abstraction for a term structure, and can be conceptually considered like an Rc<Term> with a ton of caching
/// Due to interning, hashing and equality testing is O(n)
/// Also caches many functions on each term
#[derive(Clone,PartialEq, Eq, Hash,PartialOrd, Ord)]
pub struct ContainedTerm(Unique<GM,Term>);

#[memoize]
fn ct_typed(this: ContainedTerm) -> Res<ContainedTerm> {
    this.pop().typed()
}

#[memoize]
fn ct_subst(this: ContainedTerm, other: ContainedTerm, layer: Natural) -> Res<ContainedTerm> {
    this.pop().subst(other,layer)
}

#[memoize]
fn ct_push_scope(this: ContainedTerm, n: Natural) -> Res<ContainedTerm> {
    this.pop().push_scope(n)
}

#[memoize]
fn ct_well_typed(this: ContainedTerm, ctx: Context) -> Res<()> {
    this.pop().well_typed(ctx)
}

/// Creates a new error type with the &str as a message
#[track_caller]
pub fn err_str<T>(s: &str) -> Res<T> {
    Err(ErrorType::new(s.to_string())).blame()
}

/// Creates a new error type with the String as a message
#[track_caller]
pub fn err_string<T>(s: String) -> Res<T> {
    Err(ErrorType::new(s)).blame()
}

impl ContainedTerm {
    /// Clones the inner value and returns it
    pub fn pop(self) -> Term {
        self.0.clone_inner()
    }
    #[track_caller]
    fn new(v: Term) -> Res<Self> {
        v.reduce().blame()
    }
    fn new_unchecked(v: Term) -> Self {
        Self(Unique::new(Rc::new(v),GM))
    }
    /// Attempts to get the type of the inner value, returning a result
    #[track_caller]
    pub fn typed(self) -> Res<Self> {
        ct_typed(self).blame()
    }
    #[track_caller]
    fn type_max(self, other: Self) -> Res<Self> {
        Self::new(self.pop().type_max(other.pop())?).blame()
    }
    
    #[track_caller]
    fn subst(self, other: Self, layer: Natural) -> Res<Self> {
        ct_subst(self,other,layer).blame()
    }
    /// Add a layer of scoping to the term here, effectively mimicking adding a lambda abstraction
    /// For example, (ctx: x) λ z => x when applied with push_scope 0 would become (ctx: x, y) λ z => x
    /// Useful for tracking types when they enter a lambda or leave a lambda
    /// You will likely only use this if trying to write a pretty-printer for a ContainedTerm
    #[track_caller]
    pub fn push_scope(self, n: Natural) -> Res<Self> {
        ct_push_scope(self,n).blame()
    }
    fn check_equal(self, other: Self) -> bool {
        self.eq(&other)
    }
    /// Checks if a term is refl (or constant) with an example value
    /// The specific example value does not matter, but is used internally
    /// For example, λ x => 0 or λ x => 4 would return true
    /// However, λ x => x would return false
    pub fn check_refl(self,example: Self) -> Res<Option<Self>> {
        let result = App(self.clone(),example).ctn().blame()?;
        Ok(match self.pop() {
            Lam(_,x,_) => if (result.clone().push_scope(0u8.into())?==x) {Some(result)} else {None},
            _ => None
        })
    }
    /// Checks if a term is constant upon a certain layer
    /// 0 would be a constant in layer "x"
    /// x would not be a constant in layer "x", but would be a constant in layer "y"
    pub fn check_const(self, layer: Natural) -> Res<Self> {
        self.pop().check_const(layer)
    }
    /// Convert a term into a number, if it is a natural number
    pub fn get_number(self) -> Option<usize> {
        match self.pop() {
            Zero => Some(0),
            Succ(v) => v.get_number().map(|v|{v+1}),
            _ => None,
        }
    }
    #[track_caller]
    fn well_typed(self, context: Context) -> Res<()> {
        ct_well_typed(self, context).blame()
    }
}

impl std::fmt::Debug for ContainedTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f,"{:?}",&self.0)
    }
}

/// A Term represents pretty much anything in the type system
#[derive(Clone,PartialEq, Eq, Debug, Hash)]
pub enum Term { // every term is a type
    /// DeBruijin is conceptually a variable
    /// The number inside indicates how many lambdas outside of it hold the variable
    /// For example, in λ x => λ y => x, the return value, "x" would have an index of 1, but in λ x => λ y => y, the return value "y", would have an index of 0.
    /// DeBruijin(Index,Type)
    DeBrujin(Natural,ContainedTerm), // next term is its type
    /// A lambda abstraction
    /// It is not recommended to use this directly, as the [lam_helper] and [lam_helper_poly] functions handle De Bruijn indices for you
    /// Does eta-reduction -- λ x => f x reduces to f
    /// Lam(Type,Rvalue,VariableName)
    Lam(ContainedTerm,ContainedTerm,Naming), // lam _: 0 => 1{_}
    /// Basically the same as lambda, but the rvalue indicates the return type of the lambda that it types
    /// Similarly to [Lam], not recommended to be used directly, refer to [pi_helper] and [pi_helper_poly] instead.
    /// Pi(Type,Rtype,VariableName)
    Pi(ContainedTerm,ContainedTerm,Naming), // pi _: 0, 1{_}
    /// A function application, which reduces if the input function is a concrete lambda and not a variable
    /// App(Function,Value)
    App(ContainedTerm,ContainedTerm),
    /// A type universe, of which none are impredicative.  The lack of impredicativity may be changed in the future
    Universe(Natural),
    /// The type of natural numbers
    Nat,
    /// The natural number zero
    Zero,
    /// The successor of a natural number
    Succ(ContainedTerm), // +1
    /// The natural induction principle
    /// the type of this for some number m is Π (F: ℕ → Type) (init: F 0) (next: Π (n: ℕ) (x: F n), F (S n)), F m
    /// reduces on any number [Zero] or [Succ]
    /// NatInd(Number,Universe)
    NatInd(ContainedTerm,Natural), // value upon which nat_ind is called
    /// The interval type -- it has no inductor or recursor so [IA] and [IB] may not be distinguished
    II, 
    /// The first element of the interval type
    IA,
    /// The second element of the interval type
    IB,
    /// The not function on the interval type
    /// Not([IA]) = [IB] and Not([IB]) = [IA]
    /// Not(Not(i)) = i
    Not(ContainedTerm),
    /// The and function on the interval type
    /// And([IA],_) = [IA]; And(_,[IA]) = [IA]; And([IB],i) = i; And(i,[IB]) = i;
    And(ContainedTerm,ContainedTerm),
    /// Converts a function f: Π (i: [II]) => T{i} to a value of Eq(λ (i: [II]) => T{i},f [IA],f [IB])
    /// Records endpoints of function
    EqLam(ContainedTerm),
    /// The dependent equality type
    /// Eq(Family,First,Second)
    /// When the family is constant, behaves like the standard equality type First = Second
    Eq(ContainedTerm,ContainedTerm,ContainedTerm), // Eq (F: II -> Type) (fa: F IA) (fb: F IB)
    /// Equality application -- unwraps the function represented by a value of type Eq, and computes the result
    /// Definitionally computes when applied value is [IA] or [IB]
    /// EqUw(EqLam(x),i) = x i
    /// EqUw(?: Eq(_,a,b),[IA]) = a
    /// EqUw(?: Eq(_,a,b),[IB]) = b
    EqUw(ContainedTerm,ContainedTerm), // Unwrap an element of Eq into a function that definitionally computes, and apply it
    /// Homogenous composition operator
    /// Basically, given a family over two interval values
    /// Compose three paths along the edges of the family
    /// returns a value upon the path family I₁
    /// dependent triple-composition
    /// given a = b, a = c, b = d, then c = d
    /// As of right now, HComp does not compute very well, but non-equality terms will still compute when transported over it.
    HComp{
        /// A function II -> II -> Type indicating the family over which to compose
        family: ContainedTerm, // II -> II -> Type
        /// The base path is a path ?a = ?b ? family I₀ i
        base: ContainedTerm, 
        /// The first path is a path ?a = ?c ? family i I₀
        first: ContainedTerm, 
        /// The second path is a path ?b = ?d ? family i I₁
        second: ContainedTerm, 
    }, // ?c = ?d ? family I₁ i
    /// Transport operator
    /// Transp(function: [II] -> Type, v: f [IA]): f [IB]
    Transp(ContainedTerm,ContainedTerm), // f : II -> Type -> f IA -> f IB
    /// Dependent sum type
    /// Sig(family: ?A -> ?B): Type{max(universe of A, universe of B)}
    Sig(ContainedTerm), // Sig works on a function
    /// A pair is a specific instance of a [Sig]
    /// Pair(family: ?A -> ?B, a: A, b: F a): [Sig](family)
    Pair(ContainedTerm,ContainedTerm,ContainedTerm), // Pair(F: A -> Type, a: A, F a)
    /// Dependent sum type induction principle
    /// SigInd(x): ∀ T: Sig B -> Type, q: (∀ a: A, b: B a, T (sig B a b)), T x
    /// 
    /// SigInd(Pair(F,a,b)) = λ T: Sig B -> Type, q: (∀ a: A, b: B a, T (sig B a b)), q a b
    SigInd(ContainedTerm,Natural),
}

#[derive(Clone,PartialEq, Eq, Hash, Debug)]
struct Context {
    data: Vec<ContainedTerm>,
}

impl Context {
    fn push(self,v: ContainedTerm) -> Res<Self> {
        let mut this = self.push_scope()?;
        this.data.push(v.push_scope(0u8.into())?);
        Ok(this)
    }
    fn push_scope(self) -> Res<Self> {
        let mut data = Vec::new();
        for item in self.data {
            data.push(item.push_scope(0u8.into())?);
        }
        Ok(Self{data})
    }
    fn get(&self, n: usize) -> Option<&ContainedTerm> {
        if (n>=self.data.len()) {return None}
        self.data.get(self.data.len()-1-n)
    }
    fn new() -> Self {
        Self{data: Vec::new()}
    }
}

use Term::*;

/// Helper to create a lambda
/// the first array is the objects to bring inside the lambda
/// the second value is the type of the parameter
/// the third value is the name of the parameter
/// and the final function is the 
pub fn lam_helper<const N: usize>(sp: [ContainedTerm; N], ty: ContainedTerm, name: impl Into<Naming>, f: impl Fn([ContainedTerm; N], ContainedTerm) -> Res<ContainedTerm> + 'static) -> Res<ContainedTerm> {
    let mut sp2: [ContainedTerm; N] = array::from_fn(|v|{II.ctn().unwrap()});
    let mut sp = sp.into_iter();
    for i in 0..N {
        sp2[i] = sp.next().unwrap().push_scope(0u8.into())?;
    }
    let sp = sp2;
    let arg = DeBrujin(0u8.into(), ty.clone().push_scope(0u8.into())?).ctn()?;
    Lam(ty,f(sp,arg)?,name.into()).ctn()
}


/// the same as [lam_helper], but the extra array allows universe levels to be brought into the body of the lambda for polymorphism
pub fn lam_helper_poly<const N: usize, const M: usize>(sp: [ContainedTerm; N], ty: ContainedTerm, name: impl Into<Naming>, nums: [Natural; M], f: impl Fn([ContainedTerm; N], ContainedTerm, [Natural; M]) -> Res<ContainedTerm> + 'static) -> Res<ContainedTerm> {
    lam_helper(sp,ty,name,move |sp,ty|{
        f(sp,ty,nums)
    })
}

/// the same as [lam_helper], but to describe the dependent function type rather than the lambda expression
pub fn pi_helper<const N: usize>(sp: [ContainedTerm; N], ty: ContainedTerm, name: impl Into<Naming>, f: impl Fn([ContainedTerm; N], ContainedTerm) -> Res<ContainedTerm> + 'static) -> Res<ContainedTerm> {
    let mut sp2: [ContainedTerm; N] = array::from_fn(|v|{II.ctn().unwrap()});
    let mut sp = sp.into_iter();
    for i in 0..N {
        sp2[i] = sp.next().unwrap().push_scope(0u8.into())?;
    }
    let sp = sp2;
    let arg = DeBrujin(0u8.into(), ty.clone().push_scope(0u8.into())?).ctn()?;
    Pi(ty,f(sp,arg)?,name.into()).ctn()
}

/// the same as [lam_helper_poly], but to describe the dependent function type rather than the lambda expression
pub fn pi_helper_poly<const N: usize, const M: usize>(sp: [ContainedTerm; N], ty: ContainedTerm, name: impl Into<Naming>, nums: [Natural; M], f: impl Fn([ContainedTerm; N], ContainedTerm, [Natural; M]) -> Res<ContainedTerm> + 'static) -> Res<ContainedTerm> {
    pi_helper(sp,ty,name,move |sp,ty|{
        f(sp,ty,nums)
    })
}

/// Create a function that extracts the first value of a Sig(family) when applied to it
#[track_caller]
pub fn sig_ex0(family: ContainedTerm) -> Res<ContainedTerm> {
    let A0 = match family.clone().typed()?.pop() {
        Pi(A0,_,_) => A0,
        _ => Err(ErrorType::new("Something is wrong with the family in sig_ex0 call".to_string())).blame()?
    };
    let ty0l = match A0.clone().typed()?.pop() {Universe(n) => n, _ => Err(ErrorType::new("Something is wrong with the family in sig_ex0 call".to_string())).blame()?};
    lam_helper([A0,family.clone()],Sig(family).ctn()?,"outer_sig",move |[A0,family],value|{
        App(App(SigInd(value,ty0l.clone()).ctn()?,lam_helper([A0.clone()],Sig(family.clone()).ctn()?,"sig",|[A0],_|{Ok(A0)})?).ctn()?,
        lam_helper([family],A0,"sig_a",|[family],a|{
            lam_helper([a.clone()],App(family,a).ctn()?,"sig_b",|[a],b|{
                // T (Sig f a b)
                Ok(a)
            })
        })?
    ).ctn()
    })
}

/// Create a function that extracts the dependent second value of a Sig(family) when applied to it -- typed v: Sig(family) -> family ([sig_ex0] v)
pub fn sig_ex1(family: ContainedTerm) -> Res<ContainedTerm> {
    let A0 = match family.clone().typed()?.pop() {
        Pi(A0,_,_) => A0,
        _ => Err(ErrorType::new("Something is wrong with the family in sig_ex1 call".to_string())).blame()?
    };
    let ty0l = match A0.clone().typed()?.pop() {Universe(n) => n, _ => Err(ErrorType::new("Something is wrong with the family in sig_ex1 call".to_string())).blame()?};
    let ty1l = match family.clone().typed()?.pop() {
        Pi(_,A1,_) => match A1.clone().typed()?.pop() {Universe(n) => n, _ => Err(ErrorType::new("Something is wrong with the family in sig_ex1 call".to_string())).blame()?},
        _ => Err(ErrorType::new("Something is wrong with the family in sig_ex1 call".to_string())).blame()?
    };
    lam_helper([A0,family.clone()],Sig(family).ctn()?,"outer_sig",move |[A0,family],value|{
        App(App(SigInd(value,ty1l.clone()).ctn()?,lam_helper([family.clone()],Sig(family.clone()).ctn()?,"sig",|[family],x|{
            App(family.clone(),App(sig_ex0(family.clone())?,x).ctn()?).ctn()
        })?).ctn()?,lam_helper([family],A0,"sig_a",|[family],a|{
            lam_helper([a.clone()],App(family,a).ctn()?,"sig_b",|[a],b|{
                // T (Sig f a b)
                Ok(b)
            })
        })?).ctn()
    })
}

impl Term {
    /// Convert a term into a [ContainedTerm], reducing it in the process as all contained terms are reducted.
    /// If it fails to reduce, return an error value
    #[track_caller]
    pub fn ctn(self) -> Res<ContainedTerm> {
        ContainedTerm::new(self)
    }
    fn ctn_unchecked(self) -> ContainedTerm {
        ContainedTerm::new_unchecked(self)
    }
    fn check_const(self, layer: Natural) -> Res<ContainedTerm> {
        match self {
            DeBrujin(n, ty) => match n.cmp(&layer) {
                Ordering::Equal => err_str("value is not const!")?,
                Ordering::Less => DeBrujin(n, ty.check_const(layer)?),
                Ordering::Greater => DeBrujin(n.pred(), ty.check_const(layer)?)
            }
            Lam(ty,body,name) => Lam(ty.check_const(layer.clone())?, body.check_const(layer.suc())?,name),
            Pi(ty,body,name ) => Pi(ty.check_const(layer.clone())?, body.check_const(layer.suc())?,name),
            App(a,b) => App(a.check_const(layer.clone())?,b.check_const(layer)?),
            Universe(n) => Universe(n),
            Nat => Nat,
            Zero => Zero,
            Succ(a) => Succ(a.check_const(layer)?),
            NatInd(a,n) => NatInd(a.check_const(layer)?,n),
            II => II,
            IA => IA,
            IB => IB,
            Not(a) => Not(a.check_const(layer)?),
            And(a,b) => And(a.check_const(layer.clone())?, b.check_const(layer)?),
            Eq(a,b,c) => Eq(a.check_const(layer.clone())?, b.check_const(layer.clone())?, c.check_const(layer)?),
            EqLam(a) => EqLam(a.check_const(layer)?),
            EqUw(a,b) => EqUw(a.check_const(layer.clone())?,b.check_const(layer)?),
            HComp { family, base, first, second } => HComp { family: family.check_const(layer.clone())?, base: base.check_const(layer.clone())?, first: first.check_const(layer.clone())?, second: second.check_const(layer)? },
            Transp(a,b) => Transp(a.check_const(layer.clone())?, b.check_const(layer)?),
            Sig(f) => Sig(f.check_const(layer)?),
            Pair(a,b,c) => Pair(a.check_const(layer.clone())?, b.check_const(layer.clone())?, c.check_const(layer)?),
            SigInd(s, n) => SigInd(s.check_const(layer)?,n),
        }.ctn()
    }
    fn subst(self,other: ContainedTerm, layer: Natural) -> Res<ContainedTerm> {
        match self {
            DeBrujin(n,ty) => match n.cmp(&layer) {
                Ordering::Equal => Ok(other),
                Ordering::Less => DeBrujin(n, ty.subst(other,layer)?).ctn(),
                Ordering::Greater => DeBrujin(n.pred(), ty.subst(other,layer)?).ctn()
            }
            Lam(a,b,name) => Lam(a.subst(other.clone(),layer.clone())?,b.subst(other.push_scope(0u8.into())?,layer.suc())?,name).ctn(),
            Pi(a, b,name) => Pi(a.subst(other.clone(),layer.clone())?,b.subst(other.push_scope(0u8.into())?, layer.suc())?,name).ctn(),
            App(a, b) => App(a.subst(other.clone(),layer.clone())?,b.subst(other,layer)?).ctn(),
            Universe(natural) => Universe(natural).ctn(),
            Nat => Nat.ctn(),
            Zero => Zero.ctn(),
            Succ(a) => Succ(a.subst(other,layer)?).ctn(),
            NatInd(a,n) => NatInd(a.subst(other,layer)?,n).ctn(),
            II => II.ctn(),
            IA => IA.ctn(),
            IB => IB.ctn(),
            Not(x) => Not(x.subst(other,layer)?).ctn(),
            And(x,y) => And(x.subst(other.clone(),layer.clone())?,y.subst(other,layer)?).ctn(),
            EqLam(f) => EqLam(f.subst(other,layer)?).ctn(),
            Eq(f,fa,fb) => Eq(f.subst(other.clone(),layer.clone())?,fa.subst(other.clone(),layer.clone())?,fb.subst(other,layer)?).ctn(),
            EqUw(e,i) => EqUw(e.subst(other.clone(),layer.clone())?,i.subst(other,layer)?).ctn(),
            HComp { family, base, first, second } => HComp { family: family.subst(other.clone(),layer.clone())?, base: base.subst(other.clone(),layer.clone())?, first: first.subst(other.clone(),layer.clone())?, second: second.subst(other,layer)? }.ctn(),
            Transp(f,a) => Transp(f.subst(other.clone(),layer.clone())?,a.subst(other,layer)?).ctn(),
            Sig(f) => Sig(f.subst(other,layer)?).ctn(),
            Pair(f,a,b) => Pair(f.subst(other.clone(),layer.clone())?,a.subst(other.clone(),layer.clone())?,b.subst(other,layer)?).ctn(),
            SigInd(s,n) => SigInd(s.subst(other,layer)?,n).ctn(),
        }
    }
    fn push_scope(self, n: Natural) -> Res<ContainedTerm> {
        //         @ 1, 1++ but 0 stays
        // lam Nat, 1 0
        // -> lam Nat, 2 0
        match self {
            DeBrujin(m, ty) => if m>=n {DeBrujin(m.suc(), ty.push_scope(n)?).ctn()} else {DeBrujin(m, ty.push_scope(n)?).ctn()}
            Lam(a,b,name) => Lam(a.push_scope(n.clone())?,b.push_scope(n.suc())?,name).ctn(),
            Pi(a,b,name) => Pi(a.push_scope(n.clone())?,b.push_scope(n.suc())?,name).ctn(),
            App(a,b) => App(a.push_scope(n.clone())?,b.push_scope(n)?).ctn(),
            Universe(m) => Universe(m).ctn(),
            Nat => Nat.ctn(),
            Zero => Zero.ctn(),
            Succ(a) => Succ(a.push_scope(n)?).ctn(),
            NatInd(a, m) => NatInd(a.push_scope(n)?,m).ctn(),
            II => II.ctn(),
            IA => IA.ctn(),
            IB => IB.ctn(),
            Not(x) => Not(x.push_scope(n)?).ctn(),
            And(x,y) => And(x.push_scope(n.clone())?,y.push_scope(n)?).ctn(),
            EqLam(f) => EqLam(f.push_scope(n)?).ctn(),
            Eq(f,fa,fb) => Eq(f.push_scope(n.clone())?,fa.push_scope(n.clone())?,fb.push_scope(n)?).ctn(),
            EqUw(f,i) => EqUw(f.push_scope(n.clone())?,i.push_scope(n)?).ctn(),
            HComp { family, base, first, second } => HComp { family: family.push_scope(n.clone())?, base: base.push_scope(n.clone())?, first: first.push_scope(n.clone())?, second: second.push_scope(n)? }.ctn(),
            Transp(f,fa) => Transp(f.push_scope(n.clone())?,fa.push_scope(n)?).ctn(),
            Sig(f) => Sig(f.push_scope(n)?).ctn(),
            Pair(f,a,b) => Pair(f.push_scope(n.clone())?,a.push_scope(n.clone())?,b.push_scope(n)?).ctn(),
            SigInd(s,u) => SigInd(s.push_scope(n)?,u).ctn(),
        }
    }
    fn typed(self) -> Res<ContainedTerm> {
        Ok(match self {
            DeBrujin(n, ty) => ty,
            Lam(a,b,name) => Pi(a,b.typed()?,name).ctn()?,
            Pi(a,b,_) => a.typed()?.type_max(b.typed()?)?,
            App(a,b) => match a.typed()?.pop() {
                        Pi(arg,ab,_) => if arg.check_equal(b.clone().typed()?) {Ok(ab.subst(b,Natural::from(0u8)))} else {err_str("Application is not well_typed")},
                        _ => err_str("Application isn't even a function... "),
                    }??,
            Universe(natural) => Universe(natural.suc()).ctn()?,
            Zero => Nat.ctn()?,
            Nat => Universe(Natural::from(0u8)).ctn()?,
            Succ(_) => Nat.ctn()?,
            NatInd(term,n) => {
                match term.clone().typed()?.pop() {Nat => (), _ => err_str("term is not a nat")?};
                let u = Universe(n).ctn()?;
                let nat = Nat.ctn()?;
                let family = Pi(nat,u,"index".into()).ctn()?;
                let initial = App(DeBrujin(0u8.into(), family.clone()).ctn()?,Zero.ctn()?).ctn()?;
                let next = Pi(Nat.ctn()?,Pi(App(DeBrujin(2u8.into(), family.clone()).ctn()?,DeBrujin(0u8.into(), Nat.ctn()?).ctn()?).ctn()?,App(DeBrujin(3u8.into(), family.clone()).ctn()?,Succ(DeBrujin(1u8.into(), Nat.ctn()?).ctn()?).ctn()?).ctn()?,"cur".into()).ctn()?,"n".into()).ctn()?;
                Pi(family.clone(),Pi(initial,Pi(next,App(DeBrujin(2u8.into(), family.clone()).ctn()?,term.push_scope(0u8.into())?.push_scope(0u8.into())?.push_scope(0u8.into())?).ctn()?,"suc".into()).ctn()?,"init".into()).ctn()?,"fam".into()).ctn()?
            },
            II => Universe(0u8.into()).ctn()?, // TODO: Review the possible issues with this
            IA => II.ctn()?,
            IB => II.ctn()?,
            Not(_) => II.ctn()?,
            And(_,_) => II.ctn()?,
            EqLam(term) => {
                let fa = App(term.clone(),IA.ctn()?).ctn()?;
                let fb = App(term.clone(),IB.ctn()?).ctn()?;
                let f = match term.typed()?.pop() {Pi(i,F,name)=>Lam(i,F,name).ctn()?, _ => err_str("f is not a function")?};
                Eq(f,fa,fb).ctn()?
            },
            Eq(f,fa,fb) => {
                match f.pop() {Lam(_,f,name)=>Pi(II.ctn()?,f,name).typed()?, _ => err_str("f is not a function")?}
            },
            EqUw(e,i) => {
                match e.typed()?.pop() {
                    Eq(f,_,_) => App(f,i).ctn()?,
                    _ => err_str("e is not an eq")?
                }
            },
            Transp(f,fa) => {
                App(f,IB.ctn()?).ctn()?
            }
            HComp { family, base, first, second } => {
                let c = EqUw(first,IB.ctn().unwrap()).ctn()?;
                let d = EqUw(second,IB.ctn().unwrap()).ctn()?;
                let final_family = App(family,IB.ctn().unwrap()).ctn()?;
                Eq(final_family,c,d).ctn()?
            }
            Sig(f) => f.typed()?.typed()?,
            Pair(f,a,b) => Sig(f).ctn()?,
            SigInd(s, n) => {
                let f = match s.clone().typed()?.pop() {Sig(f)=>f,_=>err_str("impossible")?};
                let arg = match f.clone().typed()?.pop() {Pi(ty, _,_)=>ty,_=>err_str("impossible")?};
                
                let input = pi_helper_poly([],s.clone().typed()?,"sig",[n],|[],val,[n]|{Universe(n).ctn()})?;
                

                // ∀ T: Sig F -> Type, q: (∀ a: A, b: B a, T (sig B a b)), T s
                pi_helper([s,f,arg],input,"fam",|[s,f,arg],family|{
                    let initial = pi_helper([f.clone(),family.clone()],arg,"sig_a",|[f,family],a|{
                        pi_helper([family,f.clone(),a.clone()],App(f,a).ctn()?,"sig_b",|[family,f,a],b|{
                            App(family,Pair(f,a,b).ctn()?).ctn()
                        })
                    })?;
                    pi_helper([family,s],initial,"init",|[family,s],_|{
                        App(family,s).ctn()
                    })
                })?
            }
        })
    }
    fn check_equal(self,other: Self) -> bool {
        self.eq(&other)
    }
    fn reduce(self) -> Res<ContainedTerm> {
        Ok(match self {
            App(a,b) => { // a and b are already fully reduced
                match a.clone().typed()?.pop() {Pi(arg,_out,_) => {
                    if (arg.clone().check_equal(b.clone().typed()?)) {
                        match a.pop() {
                            Lam(_arg,ret,_) => ret.subst(b,Natural::from(0u8))?,
                            a => App(a.ctn()?,b).ctn_unchecked(),
                        }
                    } else {err_string(format!("application is not well typed\narg type (expected): {:?}\narg type (actual): {:?}",arg,b.clone().typed()?))?}
                }, _ => err_string(format!("function is not a function\n{:?}",a))?}
            }
            NatInd(term,un) => {
                match term.clone().pop() {
                    Zero => {
                        let u = Universe(un).ctn()?;
                        let family = Pi(Nat.ctn()?,u,"index".into()).ctn()?;
                        let initial = App(DeBrujin(0u8.into(), family.clone()).ctn()?,Zero.ctn()?).ctn()?;
                        let next = Pi(Nat.ctn()?,Pi(App(DeBrujin(2u8.into(), family.clone()).ctn()?,DeBrujin(0u8.into(), Nat.ctn()?).ctn()?).ctn()?,App(DeBrujin(3u8.into(), family.clone()).ctn()?,Succ(DeBrujin(1u8.into(), Nat.ctn()?).ctn()?).ctn()?).ctn()?,"cur".into()).ctn()?,"n".into()).ctn()?;
                        Lam(family,Lam(initial.clone(),Lam(next,DeBrujin(1u8.into(), initial).ctn()?,"next".into()).ctn()?,"init".into()).ctn()?,"fam".into()).ctn_unchecked()
                    }
                    Succ(v) => {
                        let u = Universe(un.clone()).ctn()?;
                        let family = Pi(Nat.ctn()?,u,"index".into()).ctn()?;
                        let initial = App(DeBrujin(0u8.into(), family.clone()).ctn()?,Zero.ctn()?).ctn()?;
                        let next = Pi(Nat.ctn()?,Pi(App(DeBrujin(2u8.into(), family.clone()).ctn()?,DeBrujin(0u8.into(), Nat.ctn()?).ctn()?).ctn()?,App(DeBrujin(3u8.into(), family.clone()).ctn()?,Succ(DeBrujin(1u8.into(), Nat.ctn()?).ctn()?).ctn()?).ctn()?,"cur".into()).ctn()?,"n".into()).ctn()?;
                        let base = NatInd(v.clone(),un).reduce()?;
                        Lam(family.clone(),Lam(initial.clone(),Lam(next.clone(),
                            App(App(DeBrujin(0u8.into(), next.clone().push_scope(0u8.into())?).ctn()?,v).ctn()?,
                                App(App(App(base.push_scope(0u8.into())?.push_scope(0u8.into())?.push_scope(0u8.into())?,
                                    DeBrujin(2u8.into(),family.push_scope(0u8.into())?.push_scope(0u8.into())?.push_scope(0u8.into())?).ctn()?).ctn()?,
                                    DeBrujin(1u8.into(),initial.push_scope(0u8.into())?.push_scope(0u8.into())?).ctn()?).ctn()?,
                                    DeBrujin(0u8.into(), next.push_scope(0u8.into())?).ctn()?).ctn()?)
                                .ctn()?,"next".into()).ctn()?,"init".into()).ctn()?,"fam".into()).ctn_unchecked()
                    }
                    _ => match term.clone().typed()?.pop() {
                        Nat => NatInd(term,un).ctn_unchecked(),
                        _ => err_str("term is not a nat")?
                    }
                }
            }
            SigInd(s,n) => {
                match s.clone().pop() {
                    Pair(f,a,b) => {
                        // SigInd(Pair(F,a,b)) = λ T: Sig F -> Type, q: (∀ a: A, b: F a, T (sig F a b)), q a b
                        let arg = match f.clone().typed()?.pop() {Pi(ty, _,_)=>ty,_=>err_str("impossible")?};
                        let input = pi_helper([f.clone()],arg.clone(),"sig_a",|[f],val|{App(f,val).ctn()})?;
                        lam_helper([f,a,b,arg],input,"fam",|[f,a,b,arg],family|{
                            let initial = pi_helper([f.clone(),family.clone()],arg,"sig_a",|[f,family],a|{
                                pi_helper([family,f.clone(),a.clone()],App(f,a).ctn()?,"sig_b",|[family,f,a],b|{
                                    App(family,Pair(f,a,b).ctn()?).ctn()
                                })
                            })?;
                            lam_helper([a,b],initial,"init",|[a,b],q|{
                                App(App(q,a).ctn()?,b).ctn()
                            })
                        })?
                    }
                    _ => SigInd(s,n).ctn_unchecked(),
                }
            },
            Not(i) => match i.pop() {
                IA => IB.ctn()?,
                IB => IA.ctn()?,
                Not(i) => i,
                x => Not(x.ctn()?).ctn_unchecked()
            }
            And(mut i,mut j) => {
                if (i>j) {((j,i) = (i,j))} //order terms to prevent exponential blowup
                match (i.pop(),j.pop()) {
                    (IA,_) => IA.ctn()?,
                    (_,IA) => IA.ctn()?,
                    (IB,i) => i.ctn()?,
                    (i,IB) => i.ctn()?,
                    (i,j) => And(i.ctn()?,j.ctn()?).ctn_unchecked()
                }
            },
            EqUw(e,i) => {
                match i.clone().pop() {
                    IA => match e.typed()?.pop() {
                        Eq(_,v,_) => v,
                        _ => err_str("e is not eq")?
                    },
                    IB => match e.typed()?.pop() {
                        Eq(_,_,v) => v,
                        _ => err_str("e is not eq")?
                    },
                    _ => match e.clone().pop() {
                        EqLam(x) => App(x,i).ctn()?,
                        term => {
                            match e.clone().typed()?.pop() {
                                Eq(_,_,_) => EqUw(e,i).ctn_unchecked(),
                                _ => err_str("e is not eq")?
                            }
                        },
                    },
                }
            }
            EqLam(f) => {
               match f.clone().pop() {
                    Lam(ty,body,_) => match body.pop() {
                        EqUw(e,x) => match (e.check_const(0u8.into())) {
                            Ok(e) => match x.pop() {
                                DeBrujin(n, val) => if (n==Natural::from(0u8) && val == ty) {e} else {
                                    EqLam(f).ctn_unchecked()
                                }
                                _ => EqLam(f).ctn_unchecked()
                            }
                            Err(_) => EqLam(f).ctn_unchecked()
                        }
                        _ => EqLam(f).ctn_unchecked()
                    }
                    _ => EqLam(f).ctn_unchecked()
               } 
            }
            Transp(f,x) => match f.clone().pop() {
                EqLam(g) => if (g.check_refl(IA.ctn()?)?.is_some()) {x} else {Transp(f,x).ctn_unchecked()}
                HComp { family, base, first, second } => {
                    let lfirst = Lam(II.ctn().unwrap(),first,"i".into()).ctn()?;
                    let lbase = Lam(II.ctn().unwrap(),base,"i".into()).ctn()?;
                    let lsecond = Lam(II.ctn().unwrap(),second,"i".into()).ctn()?;
                    // family: ContainedTerm, // II -> II -> Type
                    // base: ContainedTerm, // ?a = ?b ? family I₀ i
                    // first: ContainedTerm, // ?a = ?c ? family i I₀
                    // second: ContainedTerm, // ?b = ?d ? family i I₁
                    // given x: ?c find y: ?d.
                    // x over sym first, then over base, then over second
                    Transp(lsecond,Transp(lbase,Transp(lam_helper([lfirst],II.ctn().unwrap(),"i",|[lfirst],i|{
                        App(lfirst,Not(i).ctn()?).ctn()
                    })?,x).ctn()?).ctn()?).ctn()?
                }
                Lam(ii,g,iname) => match g.pop() { // g is the output
                    Pi(ty,body,tyname) => {
                        let func = x;
                        let lty = Lam(ii.clone(),ty.clone(),iname.clone()).ctn().unwrap();
                        let lbody = Lam(ii.clone(),Lam(ty.clone(),body,tyname).ctn().unwrap(),iname.clone()).ctn().unwrap();
                        let ty_IB = App(lty.clone(),IB.ctn()?).ctn()?;
                        let sym_lty = lam_helper([lty.clone()],ii.clone(),iname.clone(),|[lty],i|{
                            App(lty,Not(i).ctn()?).ctn()
                        })?;
                        lam_helper([lty,sym_lty,func],ty_IB.clone(),"input_IB",|[lty,sym_lty,func],x|{
                            let input_IA = Transp(sym_lty,x.clone()).ctn()?;
                            // typed ty{I₀}
                            // now we have output_IA = x input
                            // x is typed Pi I ty{i}, body: Type
                            let output_IA = App(App(func.clone(),IA.ctn()?).ctn()?,input_IA).ctn()?;
                            // typed body{I₀,input_IA}
                            // now we want body{I₁,input_IB}
                            // find input_IA = input_IB ? ty{i}
                            // input_IA = transp (sym p) input_IB
                            // p = lty
                            // transp (fun i => p (not i)) x = x ? p
                            // sym refl = refl definitionally -- which is nice
                            // connection square
                            // λ i => transp (fun j => p (not j) ∧ (not i)) x
                            // i = 0 -> transp p x
                            // i = 1 -> transp (refl (p 0)) x
                            // fun i => func i (transp (fun j => p (not j) ∧ (not i)) x)
                            // has I₀ ⊢ body{I₀,input_IA}, I₁ ⊢ body{I₁,input_IB}
                            let path = lam_helper([lty,func,x],II.ctn()?,"i",|[lty,func,x],i|{
                                App(App(func,i.clone()).ctn()?,Transp(lam_helper([lty,i],II.ctn()?,"j",|[lty,i],j|{
                                    App(lty,And(Not(i).ctn()?,Not(j).ctn()?).ctn()?).ctn()
                                })?,x).ctn()?).ctn()
                            })?;

                            Transp(path, output_IA).ctn()
                        })?
                    }
                    Eq(f,a,b) => {
                        // x: IA = lb IA ? lf IA
                        let lf = Lam(ii.clone(),f,"i".into()).ctn()?;
                        let la = Lam(ii.clone(),a,"j".into()).ctn()?;
                        let lb = Lam(ii.clone(),b,"j".into()).ctn()?;
                        HComp { family: lf, base: x, first: la, second: lb }.ctn()?
                    }
                    Sig(f) => {
                        let (lfa,ty0l,ty1l) = match f.clone().typed()?.pop() {
                            Pi(ty,ty1,name) => (Lam(ii.clone(),ty.clone(),name).ctn()?,{
                                //match ty.typed()?.pop() {Universe(n) => n, _ => None?}
                            },{
                                //match ty1.typed()?.pop() {Universe(n) => n, _ => None?}
                            }),
                            _ => err_str("f is not a function!")?
                        };
                        let lf = Lam(ii,f.clone(),iname).ctn()?;
                        // lfa : II -> Type
                        // lf: II -> lfa i -> Type
                        // a₀: lfa I₀
                        // b₀: lf I₀ a₀
                        // a₁ = transp lfa a₀ : lfa I₁
                        // p : lf I₀ a₀ = lf I₁ (transp lfa a₀)
                        // p = λ i => lf i (transp (λ j => lfa (i ∧ j)) a₀)
                        // b₁ = transp p b₀

                        let family0 = App(lf.clone(),IA.ctn()?).ctn()?;
                        let family1 = App(lf.clone(),IA.ctn()?).ctn()?;

                        let a0 = App(sig_ex0(family0.clone())?,x.clone()).ctn()?;
                        let b0 = App(sig_ex1(family0)?,x).ctn()?;
                        let a1 = Transp(lfa.clone(),a0.clone()).ctn()?;
                        let p = lam_helper([lf,a0,lfa],II.ctn()?,"i",|[lf,a0,lfa],i|{
                            App(App(lf,i.clone()).ctn()?,Transp(lam_helper([i,lfa],II.ctn()?,"j",|[i,lfa],j|{
                                App(lfa,And(i,j).ctn()?).ctn()
                            })?,a0).ctn()?).ctn()
                        })?;
                        let b1 = Transp(p,b0).ctn()?;

                        Pair(family1,a1,b1).ctn()?
                    }
                    _ => Transp(f,x).ctn_unchecked()
                }
                g => Transp(f,x).ctn_unchecked()
            }
            Lam(ty,body,tyname) => {
                match body.clone().pop() {
                    App(f,x) => match (f.check_const(0u8.into())) {
                        Ok(f) => match x.pop() {
                            DeBrujin(n, val) => if (n==Natural::from(0u8) && val == ty) {f} else {
                                Lam(ty,body,tyname).ctn_unchecked()
                            }
                            _ => Lam(ty,body,tyname).ctn_unchecked()
                        }
                        Err(_) => Lam(ty,body,tyname).ctn_unchecked()
                    }
                    _ => Lam(ty,body,tyname).ctn_unchecked()
                }
            }
            v => v.ctn_unchecked(),
        })
    }
    fn type_max(self, other: Self) -> Res<Self>  {
        match (self,other) {
            (Universe(a),Universe(b)) => Ok(Universe(a.max(b).clone())),
            _ => err_str("type max called on non-type")
        }
    }
    fn well_typed(self, context: Context) -> Res<()> {
        match self {
            DeBrujin(natural, contained_term) => {
                check_eq(context.get(unwrap_natural(natural)),Some(&contained_term))
            },
            Lam(contained_term, contained_term1,_) => {contained_term.clone().well_typed(context.clone())?; contained_term1.well_typed(context.push(contained_term)?)},
            Pi(contained_term, contained_term1,_) => {contained_term.clone().well_typed(context.clone())?; contained_term1.well_typed(context.push(contained_term)?)},
            App(f, x) => {f.clone().well_typed(context.clone())?; x.clone().well_typed(context)?; match f.typed()?.pop() {
                Pi(arg,_,_) => check_eq(x.typed(), Ok(arg)),
                _ => err_str("f is not a function!"),
            }},
            Universe(natural) => Ok(()),
            Nat => Ok(()),
            Zero => Ok(()),
            Succ(contained_term) => {check_eq(contained_term.clone().typed(),Nat.ctn())?; contained_term.well_typed(context)},
            NatInd(contained_term, natural) => {check_eq(contained_term.clone().typed(), Nat.ctn())?; contained_term.well_typed(context)},
            II => Ok(()),
            IA => Ok(()),
            IB => Ok(()),
            Not(x) => {check_eq(x.clone().typed()?, II.ctn()?); x.well_typed(context)},
            And(x,y) => {check_eq(x.clone().typed(),II.ctn())?; check_eq(y.clone().typed(), II.ctn())?; x.well_typed(context.clone())?; y.well_typed(context)},
            EqLam(term) => {(match term.clone().typed()?.pop() {
                Pi(arg,_,_) => check_eq(arg, II.ctn()?),
                _ => err_str("term is not a lambda!"),
            })?; term.well_typed(context)},
            Eq(f,x,y) => {f.well_typed(context.clone())?; x.well_typed(context.clone())?; y.well_typed(context)},
            EqUw(e,i) => {e.well_typed(context.clone())?; i.well_typed(context.clone())},
            HComp { family, base, first, second } => {
                family.clone().well_typed(context.clone())?;
                base.clone().well_typed(context.clone())?;
                first.clone().well_typed(context.clone())?;
                second.clone().well_typed(context)?;
                match base.typed()?.pop() {Eq(f,a,b) => {
                    check_eq(f.clone(),App(family,IA.ctn().unwrap()).ctn()?)?;
                    match first.typed()?.pop() {Eq(g,a_,_) => {
                        check_eq(a_,a)?; check_eq(g,lam_helper([f.clone()], II.ctn().unwrap(),"i", |[f],i|{
                            App(App(f,i).ctn()?,IA.ctn().unwrap()).ctn()
                        })?)?;
                    }, _ => err_str("first is not an equality")?}
                    match second.typed()?.pop() {Eq(g,b_,_) => {
                        check_eq(b_,b)?; check_eq(g, lam_helper([f.clone()], II.ctn().unwrap(), "i",|[f],i|{
                            App(App(f,i).ctn()?,IB.ctn().unwrap()).ctn()
                        })?)
                    }, _ => err_str("second is not an equality")}
                }, _ => err_str("base is not an equality")}
            }
            Transp(f,x) => {check_eq(App(f.clone(),IA.ctn().unwrap()).ctn()?,x.clone())?; f.well_typed(context.clone())?; x.well_typed(context)},
            Sig(f) => f.well_typed(context),
            Pair(f,a,b) => {check_eq(App(f.clone(),a.clone()).ctn()?,b.clone().typed()?)?; f.well_typed(context.clone())?; a.well_typed(context.clone())?; b.well_typed(context)},
            SigInd(s,n) => {(match s.clone().typed()?.pop() {Sig(_)=>Ok(()),_=>err_str("It is not sigma")})?; s.well_typed(context)}
        }
    }
}

#[track_caller]
fn check_eq<A: std::fmt::Debug + std::cmp::Eq>(x: A, y: A) -> Res<()> {
    if (x==y) {Ok(())} else {err_str(&format!("{:?}!={:?}",x,y))}
}

/// Check if a value is well typed, and print its type
pub fn check(t: ContainedTerm) {
    match (t.clone().well_typed(Context::new())) {
        Ok(_) => println!("Well typed!"),
        Err(v) => println!("Not well typed! {}",v),
    }
    println!("{:?}",t.typed());
}

/// Create a [ContainedTerm] of type [Nat] that represents the number given
/// O(n) time
pub fn num(x: usize) -> ContainedTerm {
    let mut base = Zero.ctn().unwrap();
    for i in 0..x {
        base = Succ(base).ctn().unwrap()
    }
    base
}