
use std::thread::sleep;

use crate::{ctypes::{ContainedTerm, Res, Term::*, check, lam_helper, num, pi_helper}, display::{AliasMap, pretty_print_base}, equals::{refl, split_path, straight_eq}, impossible::FalseData};

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

/// In development
pub fn run() -> Res<()> {
    let family = Lam(Nat.ctn()?,Pi(Nat.ctn()?,Nat.ctn()?,"n".into()).ctn()?,"_".into()).ctn()?;
    let id_nat = lam_helper([], Nat.ctn()?, "n", |[],n|{Ok(n)})?;
    let fn_succ_nat = lam_helper([],Nat.ctn()?,"_",|_,_|{lam_helper([],Pi(Nat.ctn()?,Nat.ctn()?,"n".into()).ctn()?,"f",|[],f|{
        lam_helper([f],Nat.ctn()?,"n",|[f],n|{Succ(App(f,n).ctn()?).ctn()})
    })})?;
    let add = lam_helper([family,id_nat,fn_succ_nat], Nat.ctn()?, "n", |[family,id_nat,fn_succ_nat],n|{
        App(App(App(NatInd(n, 0u8.into()).ctn()?,family).ctn()?,id_nat).ctn()?,fn_succ_nat).ctn()
    })?;


    let add_0_l = lam_helper([add.clone()],Nat.ctn()?,"n",|[add],n|{
        let inner = App(NatInd(n, 0u8.into()).ctn()?,lam_helper([add.clone()], Nat.ctn()?, "n", |[add],n|{
            straight_eq(App(App(add,n.clone()).ctn()?,Zero.ctn()?).ctn()?, n)
        })?).ctn()?;

        App(App(inner,refl(Zero.ctn()?)?).ctn()?,lam_helper([add], Nat.ctn()?, "n", |[add],n|{
            lam_helper([], straight_eq(App(App(add,n.clone()).ctn()?,Zero.ctn()?).ctn()?,Zero.ctn()?)?, "h", |[],h|{
                EqLam(lam_helper([h], II.ctn()?, "i", |[h],i|{
                    Succ(EqUw(h, i).ctn()?).ctn()
                })?).ctn()
            })
        })?).ctn()
    })?;
    
    println!("{}",App(App(add,num(60)).ctn()?,num(15)).ctn()?.get_number().unwrap());
    Ok(())
}