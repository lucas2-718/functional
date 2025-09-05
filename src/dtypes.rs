use std::{cell::RefCell, cmp::Ordering, collections::HashSet, rc::Rc};

use malachite_nz::natural::Natural;
use memoize::memoize;
use crate::unique::{Unique,GlobalMap};

thread_local! {static SM: RefCell<HashSet<Rc<Term>>> = RefCell::new(HashSet::new());}

fn unwrap_natural(n: Natural) -> usize {
    let v = n.into_limbs_asc();
    if (v.len()>1) {panic!()};
    v[0].try_into().unwrap()
}

#[derive(Hash,Eq,PartialEq,Clone)]
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

#[derive(Clone,PartialEq, Eq, Hash)]
pub struct ContainedTerm(Unique<GM,Term>);

#[memoize]
fn ct_typed(this: ContainedTerm) -> Option<ContainedTerm> {
    this.pop().typed()
}

#[memoize]
fn ct_subst(this: ContainedTerm, other: ContainedTerm, layer: Natural) -> Option<ContainedTerm> {
    this.pop().subst(other,layer)
}

#[memoize]
fn ct_push_scope(this: ContainedTerm, n: Natural) -> Option<ContainedTerm> {
    this.pop().push_scope(n)
}


impl ContainedTerm {
    pub fn pop(self) -> Term {
        self.0.clone_inner()
    }
    fn new(v: Term) -> Option<Self> {
        v.reduce()
    }
    fn new_unchecked(v: Term) -> Self {
        Self(Unique::new(Rc::new(v),GM))
    }
    fn typed(self) -> Option<Self> {
        ct_typed(self)
    }
    fn type_max(self, other: Self) -> Option<Self> {
        Self::new(self.pop().type_max(other.pop())?)
    }
    fn subst(self, other: Self, layer: Natural) -> Option<Self> {
        ct_subst(self,other,layer)
    }
    pub fn push_scope(self, n: Natural) -> Option<Self> {
        ct_push_scope(self,n)
    }
    fn check_equal(self, other: Self) -> bool {
        self.eq(&other)
    }
    pub fn get_number(self) -> Option<usize> {
        match self.pop() {
            Zero => Some(0),
            Succ(v) => v.get_number().map(|v|{v+1}),
            _ => None,
        }
    }
    pub fn well_typed(self, context: Context) -> bool {
        todo!()
    }
}

impl std::fmt::Debug for ContainedTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f,"{:?}",&self.0)
    }
}

#[derive(Clone,PartialEq, Eq, Debug, Hash)]
pub enum Term { // every term is a type
    DeBrujin(Natural,ContainedTerm), // next term is its type
    Lam(ContainedTerm,ContainedTerm), // lam _: 0 => 1{_}
    Pi(ContainedTerm,ContainedTerm), // pi _: 0, 1{_}
    App(ContainedTerm,ContainedTerm),
    Universe(Natural),
    Nat,
    Zero,
    Succ(ContainedTerm), // +1
    NatInd(ContainedTerm,Natural), // value upon which nat_ind is called
    Refl(ContainedTerm), // refl 0
    Eq(ContainedTerm,ContainedTerm), // 0 == 1
    EqInd(ContainedTerm,Natural), // value upon which eq_ind is called, produces the final function
}

#[derive(Clone)]
struct Context {
    data: Vec<ContainedTerm>,
}

impl Context {
    fn push(mut self,v: ContainedTerm) -> Self {
        self.data.push(v);
        self
    }
}

use Term::*;

impl Term {
    pub fn ctn(self) -> Option<ContainedTerm> {
        ContainedTerm::new(self)
    }
    fn ctn_unchecked(self) -> ContainedTerm {
        ContainedTerm::new_unchecked(self)
    }
    fn subst(self,other: ContainedTerm, layer: Natural) -> Option<ContainedTerm> {
        Some(match self {
            DeBrujin(n,ty) => match n.cmp(&layer) {
                Ordering::Equal => other,
                Ordering::Less => DeBrujin(n, ty.subst(other,layer)?).ctn()?,
                Ordering::Greater => DeBrujin(n - Natural::from(1u8), ty.subst(other,layer)?).ctn()?
            }
            Lam(a,b) => Lam(a.subst(other.clone(),layer.clone())?,b.subst(other.push_scope(0u8.into())?,layer + Natural::from(1u8))?).ctn()?,
            Pi(a, b) => Pi(a.subst(other.clone(),layer.clone())?,b.subst(other.push_scope(0u8.into())?, layer + Natural::from(1u8))?).ctn()?,
            App(a, b) => App(a.subst(other.clone(),layer.clone())?,b.subst(other,layer)?).ctn()?,
            Refl(a) => Refl(a.subst(other,layer)?).ctn()?,
            Eq(a, b) => Eq(a.subst(other.clone(),layer.clone())?,b.subst(other,layer)?).ctn()?,
            Universe(natural) => Universe(natural).ctn()?,
            Nat => Nat.ctn()?,
            Zero => Zero.ctn()?,
            Succ(a) => Succ(a.subst(other,layer)?).ctn()?,
            NatInd(a,n) => NatInd(a.subst(other,layer)?,n).ctn()?,
            EqInd(a,n) => EqInd(a.subst(other,layer)?,n).ctn()?,
        })
    }
    fn push_scope(self, n: Natural) -> Option<ContainedTerm> {
        //         @ 1, 1++ but 0 stays
        // lam Nat, 1 0
        // -> lam Nat, 2 0
        Some(match self {
            DeBrujin(m, ty) => if m>=n {DeBrujin(m + Natural::from(1u8), ty.push_scope(n)?).ctn()?} else {DeBrujin(m, ty.push_scope(n)?).ctn()?}
            Lam(a,b) => Lam(a.push_scope(n.clone())?,b.push_scope(n + Natural::from(1u8))?).ctn()?,
            Pi(a,b) => Pi(a.push_scope(n.clone())?,b.push_scope(n + Natural::from(1u8))?).ctn()?,
            App(a,b) => App(a.push_scope(n.clone())?,b.push_scope(n)?).ctn()?,
            Refl(a) => Refl(a.push_scope(n)?).ctn()?,
            Eq(a,b) => Eq(a.push_scope(n.clone())?,b.push_scope(n)?).ctn()?,
            Universe(m) => Universe(m).ctn()?,
            Nat => Nat.ctn()?,
            Zero => Zero.ctn()?,
            Succ(a) => Succ(a.push_scope(n)?).ctn()?,
            NatInd(a, m) => NatInd(a.push_scope(n)?,m).ctn()?,
            EqInd(a, m) => EqInd(a.push_scope(n)?, m).ctn()?,
        })
    }
    fn typed(self) -> Option<ContainedTerm> {
        Some(match self {
            DeBrujin(n, ty) => ty,
            Lam(a,b) => Pi(a,b.typed()?).ctn()?,
            Pi(a,b) => a.typed()?.type_max(b.typed()?)?,
            App(a,b) => match a.typed()?.pop() {
                        Pi(arg,ab) => if arg.check_equal(b.clone().typed()?) {Some(ab.subst(b,Natural::from(0u8)))} else {None},
                        _ => None
                    }??,
            Universe(natural) => Universe(natural + Natural::from(1u8)).ctn()?,
            Zero => Nat.ctn()?,
            Nat => Universe(Natural::from(0u8)).ctn()?,
            Succ(_) => Nat.ctn()?,
            NatInd(term,n) => {
                match term.clone().typed()?.pop() {Nat => (), _ => None?};
                let u = Universe(n).ctn()?;
                let nat = Nat.ctn()?;
                let family = Pi(nat,u).ctn()?;
                let initial = App(DeBrujin(0u8.into(), family.clone()).ctn()?,Zero.ctn()?).ctn()?;
                let next = Pi(Nat.ctn()?,Pi(App(DeBrujin(2u8.into(), family.clone()).ctn()?,DeBrujin(0u8.into(), Nat.ctn()?).ctn()?).ctn()?,App(DeBrujin(3u8.into(), family.clone()).ctn()?,Succ(DeBrujin(1u8.into(), Nat.ctn()?).ctn()?).ctn()?).ctn()?).ctn()?).ctn()?;
                Pi(family.clone(),Pi(initial,Pi(next,App(DeBrujin(2u8.into(), family.clone()).ctn()?,term.push_scope(0u8.into())?.push_scope(0u8.into())?.push_scope(0u8.into())?).ctn()?).ctn()?).ctn()?).ctn()?
            },
            Refl(term) => Eq(term.clone(),term).ctn()?,
            Eq(term, _) => term.typed()?.typed()?,
            EqInd(term,n) => {
                let u = Universe(n).ctn()?;
                let (x,y) = match term.clone().typed()?.pop() {Eq(a,b) => (a,b), _ => None?};
                let ty = x.clone().typed()?;
                // family = Pi (x y: T) (h: x==y), U
                // initial = Pi (x: T), family x x (refl x)
                // function {x y h} = Pi (f: family), f x y h
                // implicit x y is acceptable because they can be derived from type(h)
                let family = Pi(ty.clone(),Pi(ty.clone(),Pi(Eq(DeBrujin(1u8.into(), ty.clone()).ctn()?,DeBrujin(0u8.into(), ty.clone()).ctn()?).ctn()?,u).ctn()?).ctn()?).ctn()?;
                let initial = Pi(ty.clone(),App(App(App(DeBrujin(1u8.into(), family.clone()).ctn()?,DeBrujin(0u8.into(), ty.clone()).ctn()?).ctn()?,DeBrujin(0u8.into(), ty.clone()).ctn()?).ctn()?,Refl(DeBrujin(0u8.into(), ty.clone()).ctn()?).ctn()?).ctn()?).ctn()?;
                Pi(family.clone(),Pi(initial,App(App(App(DeBrujin(1u8.into(), family.clone()).ctn()?,x).ctn()?,y).ctn()?,term).ctn()?).ctn()?).ctn()?
            },
        })
    }
    fn check_equal(self,other: Self) -> bool {
        self.eq(&other)
    }
    fn reduce(self) -> Option<ContainedTerm> {
        Some(match self {
            App(a,b) => { // a and b are already fully reduced
                match a.clone().typed()?.pop() {Pi(arg,_out) => {
                    if (arg.check_equal(b.clone().typed()?)) {
                        match a.pop() {
                            Lam(_arg,ret) => ret.subst(b,Natural::from(0u8))?,
                            a => App(a.ctn()?,b).ctn_unchecked(),
                        }
                    } else {None?}
                }, _ => None?}
            }
            NatInd(term,un) => {
                match term.clone().pop() {
                    Zero => {
                        let u = Universe(un).ctn()?;
                        let family = Pi(Nat.ctn()?,u).ctn()?;
                        let initial = App(DeBrujin(0u8.into(), family.clone()).ctn()?,Zero.ctn()?).ctn()?;
                        let next = Pi(Nat.ctn()?,Pi(App(DeBrujin(2u8.into(), family.clone()).ctn()?,DeBrujin(0u8.into(), Nat.ctn()?).ctn()?).ctn()?,App(DeBrujin(3u8.into(), family.clone()).ctn()?,Succ(DeBrujin(1u8.into(), Nat.ctn()?).ctn()?).ctn()?).ctn()?).ctn()?).ctn()?;
                        Lam(family,Lam(initial.clone(),Lam(next,DeBrujin(1u8.into(), initial).ctn()?).ctn()?).ctn()?).ctn_unchecked()
                    }
                    Succ(v) => {
                        let u = Universe(un.clone()).ctn()?;
                        let family = Pi(Nat.ctn()?,u).ctn()?;
                        let initial = App(DeBrujin(0u8.into(), family.clone()).ctn()?,Zero.ctn()?).ctn()?;
                        let next = Pi(Nat.ctn()?,Pi(App(DeBrujin(2u8.into(), family.clone()).ctn()?,DeBrujin(0u8.into(), Nat.ctn()?).ctn()?).ctn()?,App(DeBrujin(3u8.into(), family.clone()).ctn()?,Succ(DeBrujin(1u8.into(), Nat.ctn()?).ctn()?).ctn()?).ctn()?).ctn()?).ctn()?;
                        let base = NatInd(v.clone(),un).reduce()?;
                        Lam(family.clone(),Lam(initial.clone(),Lam(next.clone(),
                            App(App(DeBrujin(0u8.into(), next.clone().push_scope(0u8.into())?).ctn()?,v).ctn()?,
                                App(App(App(base.push_scope(0u8.into())?.push_scope(0u8.into())?.push_scope(0u8.into())?,
                                    DeBrujin(2u8.into(),family.push_scope(0u8.into())?.push_scope(0u8.into())?.push_scope(0u8.into())?).ctn()?).ctn()?,
                                    DeBrujin(1u8.into(),initial.push_scope(0u8.into())?.push_scope(0u8.into())?).ctn()?).ctn()?,
                                    DeBrujin(0u8.into(), next.push_scope(0u8.into())?).ctn()?).ctn()?)
                                .ctn()?).ctn()?).ctn()?).ctn_unchecked()
                    }
                    _ => match term.clone().typed()?.pop() {
                        Nat => NatInd(term,un).ctn_unchecked(),
                        _ => None?
                    }
                }
            }
            EqInd(term,un) => {
                match term.pop() {
                    Refl(v) => {
                        let u = Universe(un).ctn()?;
                        let ty = v.clone().typed()?;
                        let family = Pi(ty.clone(),Pi(ty.clone(),Pi(Eq(DeBrujin(1u8.into(), ty.clone()).ctn()?,DeBrujin(0u8.into(), ty.clone()).ctn()?).ctn()?,u).ctn()?).ctn()?).ctn()?;
                        let initial = Pi(ty.clone(),App(App(App(DeBrujin(1u8.into(), family.clone()).ctn()?,DeBrujin(0u8.into(), ty.clone()).ctn()?).ctn()?,DeBrujin(0u8.into(), ty.clone()).ctn()?).ctn()?,Refl(DeBrujin(0u8.into(), ty.clone()).ctn()?).ctn()?).ctn()?).ctn()?;
                        let v = v.push_scope(0u8.into())?.push_scope(0u8.into())?;
                        Lam(family,Lam(initial.clone(),App(DeBrujin(0u8.into(), initial).ctn()?,v).ctn()?).ctn()?).ctn_unchecked()
                    }
                    _ => todo!()
                }
            }
            v => v.ctn_unchecked(),
        })
    }
    fn type_max(self, other: Self) -> Option<Self>  {
        match (self,other) {
            (Universe(a),Universe(b)) => Some(Universe(a.max(b).clone())),
            _ => None
        }
    }
    fn well_typed(self, context: Context) -> bool {
        match self {
            DeBrujin(natural, contained_term) => context.data[unwrap_natural(natural)]==contained_term,
            Lam(contained_term, contained_term1) => contained_term.clone().well_typed(context.clone()) && contained_term1.well_typed(context.push(contained_term)),
            Pi(contained_term, contained_term1) => contained_term.clone().well_typed(context.clone()) && contained_term1.well_typed(context.push(contained_term)),
            App(contained_term, contained_term1) => contained_term.well_typed(context.clone()) && contained_term1.well_typed(context),
            Universe(natural) => true,
            Nat => true,
            Zero => true,
            Succ(contained_term) => contained_term.well_typed(context),
            NatInd(contained_term, natural) => contained_term.well_typed(context),
            Refl(contained_term) => contained_term.well_typed(context),
            Eq(contained_term, contained_term1) => contained_term.clone().typed() == contained_term1.clone().typed() && contained_term.well_typed(context.clone()) && contained_term1.well_typed(context),
            EqInd(contained_term, natural) => contained_term.well_typed(context.clone()),
        }
    }
}

pub fn check(t: ContainedTerm) {
    println!("{:?}",t.typed().unwrap());
}

pub fn num(x: usize) -> ContainedTerm {
    let mut base = Zero.ctn().unwrap();
    for i in 0..x {
        base = Succ(base).ctn().unwrap()
    }
    base
}

