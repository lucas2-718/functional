use crate::{ctypes::{ContainedTerm, ErrorType, Natural, Res, Scopeless, Term::*, lam_helper, lam_helper_poly, pi_helper, pi_helper_poly}, display::{AliasMap, pretty_print_base}, equals::{cong, refl, straight_eq, transport_eq}, impossible::FalseData, numbers};

/// Basic data describing the booleans
#[derive(Clone)]
pub struct BoolData {
    /// The trimming function used internally, returns 0 if the input is zero or 1 and otherwise returns 1
    pub trim: ContainedTerm,
    /// The type of booleans, a sum requiring trim to be zero
    pub bool_type: ContainedTerm,
    /// The false boolean, of type bool_type
    pub bool_false: ContainedTerm,
    /// The true boolean, of type bool_type
    pub bool_true: ContainedTerm,
    /// The family used in the [Sig] of [BoolData::bool_type]
    pub bool_fam: ContainedTerm,
}

impl Scopeless for BoolData {}

impl BoolData {
    /// Creates a new BoolData instance
    pub fn new() -> Res<BoolData> {
        // Construct the function trim, which returns 0 if the input is zero or one, and 1 otherwise by repeated pattern matching
        
        let family = Lam(Nat.ctn()?,Nat.ctn()?,"_".into()).ctn()?;
        let trim = lam_helper([family], Nat.ctn()?, "n", |[family],n|{
            App(App(App(NatInd(n, 0u8.into()).ctn()?,family.clone()).ctn()?,Zero.ctn()?).ctn()?,lam_helper([family], Nat.ctn()?, "n-1", |[family],n|{
                lam_helper([family,n],Nat.ctn()?,"_",|[family,n],_|{
                    App(App(App(NatInd(n, 0u8.into()).ctn()?,family.clone()).ctn()?,Zero.ctn()?).ctn()?,Lam(Nat.ctn()?,Lam(Nat.ctn()?,Succ(Zero.ctn()?).ctn()?,"_".into()).ctn()?,"n2".into()).ctn()?).ctn()
                })
            })?).ctn()
        })?;

        let bfam = lam_helper([trim.clone()], Nat.ctn()?, "n", |[trim],n|{
            straight_eq(Zero.ctn()?, App(trim,n).ctn()?)
        })?;

        let bool_type = Sig(bfam.clone()).ctn()?;

        let bool_false = Pair(bfam.clone(), Zero.ctn()?, refl(Zero.ctn()?)?).ctn()?;

        let bool_true = Pair(bfam.clone(), Succ(Zero.ctn()?).ctn()?, refl(Zero.ctn()?)?).ctn()?;

        Ok(BoolData { trim, bool_type, bool_false, bool_true, bool_fam: bfam })
    }
    /// Runs the boolean induction principle on a specific instance of a boolean
    pub fn bool_ind(&self, b: ContainedTerm, n: Natural) -> Res<ContainedTerm> {
        let famtype = pi_helper_poly([], self.bool_type.clone(), "_", [n], |[],_,[n]|{Universe(n).ctn()})?;
        let ind = lam_helper_poly([b,self.trim.clone(),self.bool_false.clone(),self.bool_true.clone(),self.bool_fam.clone()], famtype, "fam", [n], |[b,trim,bfalse,btrue,bfam],fam,[n]|{
            let true_family = lam_helper([fam.clone(),bfalse.clone(),btrue.clone()], Sig(bfam.clone()).ctn()?, "b", |[fam,bfalse,btrue],b|{
                pi_helper([btrue,fam.clone(),b], App(fam,bfalse).ctn()?, "vf", |[btrue,fam,b],vf|{
                    pi_helper([fam.clone(),b], App(fam,btrue).ctn()?, "vt", |[fam,b],vt|{
                        App(fam,b).ctn()
                    })
                })
            })?;
            App(App(SigInd(b, n).ctn()?,true_family.clone()).ctn()?,lam_helper_poly([trim,fam,bfalse,btrue,bfam], Nat.ctn()?, "n", [n],|[trim,fam,bfalse,btrue,bfam],n,[u]|{
                // Goal : (hyp: 0 = trim n) -> fam (0, refl 0) -> fam (1, refl 0) -> fam (n, hyp)
                // how to prove goal
                // matching on goal
                // (hyp : 0 = 0) -> (vf: fam (0, refl 0)) -> (vt: fam (1, refl 0)) : fam (0, hyp) := transport vt over refl 0 = hyp
                // (hyp : 0 = 0) -> (vf: fam (0, refl 0)) -> (vt: fam (1, refl 0)) : fam (1, hyp) := transport vt over refl 0 = hyp
                // (hyp : 0 = 1) : (vf: fam (0, refl 0)) -> (vt: fam (1, refl 0)) -> fam (2 + n, hyp) := exfalso into the family
                let indfam = lam_helper([bfalse.clone(),btrue.clone(),fam.clone(),trim,bfam.clone()], Nat.ctn()?, "n", |[bfalse,btrue,fam,trim,bfam],n|{
                    pi_helper([n.clone(),bfalse,btrue,fam,trim.clone(),bfam], straight_eq(Zero.ctn()?,App(trim,n).ctn()?)?, "hyp", |[n,bfalse,btrue,fam,trim,bfam],hyp|{
                        pi_helper([n.clone(),btrue,fam.clone(),trim,bfam,hyp],App(fam,bfalse).ctn()?,"vf",|[n,btrue,fam,trim,bfam,hyp],_|{
                            pi_helper([n.clone(),fam.clone(),trim,bfam,hyp], App(fam,btrue).ctn()?, "vt", |[n,fam,trim,bfam,hyp],_|{
                                App(fam,Pair(bfam,n,hyp).ctn()?).ctn()
                            })
                        })
                    })
                })?;
                
                let fam0 = lam_helper([bfalse.clone(),btrue.clone(),bfam.clone(),fam.clone()],straight_eq(Zero.ctn()?, Zero.ctn()?)?,"hyp",|[bfalse,btrue,bfam,fam],hyp|{
                    lam_helper([btrue,bfam,fam.clone(),hyp],App(fam,bfalse).ctn()?,"vf",|[btrue,bfam,fam,hyp],vf|{
                        lam_helper([bfam,fam.clone(),hyp,vf], App(fam,btrue).ctn()?, "vt", |[bfam,fam,hyp,vf],vt|{
                            // goal = fam (0, hyp)
                            // have = fam (0, refl 0)
                            // refl = hyp
                            let refl_hyp = App(numbers::zero_eq_trivial()?,hyp).ctn()?;
                            // h => fam (0 , h)
                            let cong_func = lam_helper([fam,bfam],straight_eq(Zero.ctn()?, Zero.ctn()?)?,"hyp",|[fam,bfam],hyp|{
                                App(fam,Pair(bfam,Zero.ctn()?,hyp).ctn()?).ctn()
                            })?;
                            // have = goal
                            let path = cong(cong_func, refl_hyp)?;
                            transport_eq(path,vf)
                        })
                    })
                })?;

                let fam1 = lam_helper([bfalse.clone(),btrue.clone(),bfam.clone(),fam.clone()],straight_eq(Zero.ctn()?, Zero.ctn()?)?,"hyp",|[bfalse,btrue,bfam,fam],hyp|{
                    lam_helper([btrue,bfam,fam.clone(),hyp],App(fam,bfalse).ctn()?,"vf",|[btrue,bfam,fam,hyp],vf|{
                        lam_helper([bfam,fam.clone(),hyp,vf], App(fam,btrue).ctn()?, "vt", |[bfam,fam,hyp,vf],vt|{
                            // goal = fam (1, hyp)
                            // have = fam (1, refl 0)
                            // refl = hyp
                            let refl_hyp = App(numbers::zero_eq_trivial()?,hyp).ctn()?;
                            // h => fam (0 , h)
                            let cong_func = lam_helper([fam,bfam],straight_eq(Zero.ctn()?, Zero.ctn()?)?,"hyp",|[fam,bfam],hyp|{
                                App(fam,Pair(bfam,Succ(Zero.ctn()?).ctn()?,hyp).ctn()?).ctn()
                            })?;
                            // have = goal
                            let path = cong(cong_func, refl_hyp)?;
                            transport_eq(path,vt)
                        })
                    })
                })?;

                let fam2 = lam_helper([bfalse,btrue,bfam,fam.clone()],Nat.ctn()?,"n2",|[bfalse,btrue,bfam,fam],n2|{
                    lam_helper([bfalse,btrue,bfam,fam,n2], straight_eq(Zero.ctn()?, Succ(Zero.ctn()?).ctn()?)?, "hyp", |[bfalse,btrue,bfam,fam,n2],hyp|{
                        let n = Succ(Succ(n2).ctn()?).ctn()?;
                        let target = pi_helper([n.clone(),btrue,fam.clone(),bfam,hyp.clone()],App(fam,bfalse).ctn()?,"vf",|[n,btrue,fam,bfam,hyp],_|{
                            pi_helper([n.clone(),fam.clone(),bfam,hyp], App(fam,btrue).ctn()?, "vt", |[n,fam,bfam,hyp],_|{
                                App(fam,Pair(bfam,n,hyp).ctn()?).ctn()
                            })
                        })?;
                        App(FalseData::new()?.exfalso(target)?,hyp).ctn()
                    })
                })?;


                let partial = App(App(App(NatInd(n, u).ctn()?,indfam.clone()).ctn()?,fam0).ctn()?,lam_helper_poly([fam1,fam2,indfam], Nat.ctn()?, "n1", [u],|[fam1,fam2,indfam],n1,[u]|{
                    let new_indfam = lam_helper_poly([indfam.clone()], Nat.ctn()?, "n", [u],|[indfam],n,[u]|{
                        App(indfam,Succ(n).ctn()?).ctn()
                    })?;
                    lam_helper_poly([fam1,fam2,new_indfam.clone(),n1.clone()], App(indfam,n1).ctn()?, "_", [u],|[fam1,fam2,indfam,n1],_,[u]|{
                        App(App(App(NatInd(n1, u).ctn()?,indfam.clone()).ctn()?,fam1).ctn()?,lam_helper([fam2,indfam], Nat.ctn()?, "n2", |[fam2,indfam],n2|{
                            lam_helper([fam2,indfam.clone(),n2.clone()],App(indfam,n2).ctn()?,"_",|[fam2,indfam,n2],_|{
                                App(fam2,n2).ctn()
                            })
                        })?).ctn()
                    })
                })?).ctn()?;
                
                Ok(partial)
            })?).ctn()
        })?;
        
        Ok(ind)
    }
    /// Creates the boolean induction principle on a specific universe level
    pub fn generic_bool_ind(&self, n: Natural) -> Res<ContainedTerm> {
        lam_helper_poly([], self.bool_type.clone(), "b", (self.clone(),n), |[],b,(this,n)|{
            this.bool_ind(b, n)
        })
    }
}