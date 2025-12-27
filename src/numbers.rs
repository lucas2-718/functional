
use std::thread::sleep;

use crate::{ctypes::{ContainedTerm, Res, Scopeless, Term::*, check, lam_helper, num, pi_helper}, display::{AliasMap, pretty_print_base}, equals::{cong, refl, split_path, straight_eq}, impossible::FalseData};

pub fn successor_function() -> Res<ContainedTerm> {
    lam_helper([], Nat.ctn()?, "n", |[],n|{Succ(n).ctn()})
}

/// A function where 0 => 0 and _ => 1
pub fn flatten_natural(n: ContainedTerm) -> Res<ContainedTerm> {
    let fam = Pi(Nat.ctn()?,Nat.ctn()?,"_".into()).ctn()?;
    App(App(NatInd(n, 0u8.into()).ctn()?,Zero.ctn()?).ctn()?,Lam(Nat.ctn()?, Lam(Nat.ctn()?, Succ(Zero.ctn()?).ctn()?, "_".into()).ctn()?, "_".into()).ctn()?).ctn()
}

/// Proof that all values of 0=0 are in fact refl
/// term typed (h : 0 = 0) -> refl 0 = h
pub fn zero_eq_trivial() -> Res<ContainedTerm> {
    // Proving that (h : 0=0) -> refl 0 = h is relatively trivial
    // we can prove that h i = 0 via casing on what h i is and then path splitting
    // this ensures the endpoint behavior being that h i = 0 is refl and not some variant of h
    // then reassemble along the path to get the full value
    lam_helper([], straight_eq(Zero.ctn()?, Zero.ctn()?)?, "hyp", |[],hyp|{
        // izero : (i : II) -> 0 = hyp i
        // izero i0 _ = refl 0
        // izero i1 _ = refl 0
        // izero _ i0 = refl 0
        // izero _ i1 = hyp
        
        let izero = lam_helper([hyp], II.ctn()?, "i", |[hyp],i|{
            // (n : nat) -> (0 = n) -> (0 = n)
            // make an equality into a reflexive equality
            // but a different variant of this
            let fam = lam_helper([], Nat.ctn()?, "n", |[],n|{
                pi_helper([n.clone()], straight_eq(Zero.ctn()?, n)?, "_", |[n],_|{
                    straight_eq(Zero.ctn()?, n)
                })
            })?;

            // Case on the natural to ensure definitional computation on zero works correctly and then just do whatever works for the impossible case
            let func = lam_helper([fam], Nat.ctn()?, "n", |[fam],n|{
                App(App(App(NatInd(n, 0u8.into()).ctn()?,fam.clone()).ctn()?,
                    lam_helper([], straight_eq(Zero.ctn()?, Zero.ctn()?)?, "_", |[],_|{refl(Zero.ctn()?)})?).ctn()?,
                    lam_helper([fam], Nat.ctn()?, "n", |[fam],n|{
                        lam_helper([n.clone()],App(fam,n).ctn()?, "_", |[n],_|{
                            // This case is impossible, so doesn't matter as long as it type-checks
                            lam_helper([], straight_eq(Zero.ctn()?, Succ(n).ctn()?)?, "hyp", |[],hyp|{Ok(hyp)})
                        })
                    })?).ctn()
            })?;

            let split = split_path(hyp.clone(), IA.ctn()?, i.clone())?;

            // logically the same as split, but now reflexive whenever it can be
            let new_split = App(App(func,EqUw(hyp,i).ctn()?).ctn()?,split).ctn()?;

            Ok(new_split)
        })?;

        
        
        EqLam(lam_helper([izero], II.ctn()?, "i", |[izero],i|{
            EqLam(lam_helper([izero,i], II.ctn()?, "j", |[izero,i],j|{
                EqUw(App(izero,j).ctn()?,i).ctn()
            })?).ctn()
        })?).ctn()
        
    })
}


#[derive(Clone)]
pub struct NatData {
    pub add_func: ContainedTerm,
    pub add_zero_right: ContainedTerm,
    pub add_succ_right: ContainedTerm,
    pub add_sym: ContainedTerm
}

impl Scopeless for NatData {}

impl NatData {
    pub fn new() -> Res<Self> {
        let addition = lam_helper([], Nat.ctn()?, "n", |[],n|{
            let family = Lam(Nat.ctn()?,Pi(Nat.ctn()?,Nat.ctn()?,"x".into()).ctn()?,"n".into()).ctn()?;
            let base = lam_helper([], Nat.ctn()?, "x", |[],x|{Ok(x)})?;
            let step = lam_helper([],Nat.ctn()?,"n",|[],n|{
                lam_helper([], Pi(Nat.ctn()?,Nat.ctn()?,"n".into()).ctn()?, "f", |[],f|{
                    lam_helper([f], Nat.ctn()?, "x", |[f],x|{
                        // add (S n) ? = S (add n ?)
                        // there is an equivalent form of
                        // add (S n) ? = add n (S ?)
                        // but it is harder to work with definitionally
                        Succ(App(f,x).ctn()?).ctn()
                    })
                })
            })?;
            App(App(App(NatInd(n, 0u8.into()).ctn()?,family).ctn()?,base).ctn()?,step).ctn()
        })?;
        
        // add x 0 = x
        // add 0 0 = 0 -> refl
        // add (S x) 0 = S x -> cong S (prev : add x 0 = x)
        let add_zero_right = lam_helper([addition.clone()], Nat.ctn()?, "x", |[addition],x|{
            let family = lam_helper([addition.clone()], Nat.ctn()?, "x", |[addition],x|{
                straight_eq(App(App(addition,x.clone()).ctn()?,Zero.ctn()?).ctn()?, x)
            })?;
            let base = refl(Zero.ctn()?)?;
            let step = lam_helper([addition], Nat.ctn()?, "x", |[addition],x|{
                lam_helper([], straight_eq(App(App(addition,x.clone()).ctn()?,Zero.ctn()?).ctn()?, x)?, "p", |[],p|{
                    cong(successor_function()?, p)
                })
            })?;

            App(App(App(NatInd(x, 0u8.into()).ctn()?,family).ctn()?,base).ctn()?,step).ctn()
        })?;

        // add x (S y) = S (add x y)
        // add 0 (S y) = S y -> refl
        // add (S x) (S y) = S (add (S x) y)
        // ~ S (add x (S y)) = S (S (add x y)) -> cong S (prev : add x (S y) = S (add x y))
        let add_succ_right = lam_helper([addition.clone()], Nat.ctn()?, "x", |[addition],x|{
            lam_helper([addition,x], Nat.ctn()?, "y", |[addition,x],y|{
                let family = lam_helper([addition.clone(),y.clone()],Nat.ctn()?,"x",|[addition,y],x|{
                    straight_eq(App(App(addition.clone(),x.clone()).ctn()?,Succ(y.clone()).ctn()?).ctn()?, Succ(App(App(addition,x).ctn()?,y).ctn()?).ctn()?)
                })?;
                let base = refl(Succ(y.clone()).ctn()?)?;
                let step = lam_helper([family.clone()],Nat.ctn()?,"x",|[family],x|{
                    lam_helper([],App(family,x).ctn()?,"p",|[],p|{
                        cong(successor_function()?,p)
                    })
                })?;

                App(App(App(NatInd(x, 0u8.into()).ctn()?,family).ctn()?,base).ctn()?,step).ctn()
            })
        })?;

        // add x y = add y x

        // add x (S y) = add (S y) x
        // ~ add x (S y) = S (add y x)
        // -> asr x y . (? : (add y x = add x y))
        
        // add x 0 = add 0 x
        // add x 0 = x -> azr x
        

        todo!();
    }
}
