
use crate::ctypes::{ContainedTerm, Natural, Res, Term::*, lam_helper, lam_helper_poly, pi_helper_poly};

/// Split a path over two interval variables
/// Very useful for handling paths directly
/// split_path(eq,IA,IB) = eq
/// split_path(eq,IB,IA) = sym eq
/// split_path(eq,x,x) = refl (eq x)
pub fn split_path(eq: ContainedTerm, i1: ContainedTerm, i2: ContainedTerm) -> Res<ContainedTerm> {
    // (i2 and i) or (i1 and not i)
    // not (not (i2 and i) and not (i1 and not i))
    EqLam(lam_helper([eq,i1,i2], II.ctn()?, "i", |[eq,i1,i2],i|{
        EqUw(eq,
            Not(And(Not(
                And(i2,i.clone()).ctn()?
            ).ctn()?,Not(
                And(i1,Not(i).ctn()?).ctn()?
            ).ctn()?).ctn()?).ctn()?
        ).ctn()
    })?).ctn()
}

/// Transitive principle of equality, allows you to concatenate paths
/// watch out for higher paths with this one, hcomp in this prover has issues with higher paths
/// this should work at least when you would expect regular J to work, however
pub fn trans(eqA: ContainedTerm, eqB: ContainedTerm) -> Res<ContainedTerm> {
    let cfirst = EqUw(eqA.clone(),IA.ctn()?).ctn()?;
    let family = EqLam(lam_helper([eqB,cfirst], II.ctn()?, "i", |[eqB,cfirst],i|{
        straight_eq(cfirst, EqUw(eqB,i).ctn()?)
    })?).ctn()?;
    transport_eq(family, eqA)
}

/// Switch path : a = b to sym path : b = a by symmetric principle of equality
pub fn sym(eq: ContainedTerm) -> Res<ContainedTerm> {
    split_path(eq, IB.ctn()?, IA.ctn()?)
}

/// Congruent principle of equality
/// cong(func,eq: a = b) : func a = func b 
pub fn cong(func: ContainedTerm, eq: ContainedTerm) -> Res<ContainedTerm> {
    EqLam(lam_helper([func,eq], II.ctn()?, "i", |[func,eq],i|{
        App(func,EqUw(eq,i).ctn()?).ctn()
    })?).ctn()
}

/// Transport a term over an equality, because the [Transp] primitive operates on lambdas, not an equality
pub fn transport_eq(eq: ContainedTerm, begin: ContainedTerm) -> Res<ContainedTerm> {
    Transp(lam_helper([eq], II.ctn()?, "i", |[eq],i|{EqUw(eq,i).ctn()})?, begin).ctn()
}

/// Returns the type a ≡ b provided a and b are the same type
pub fn straight_eq(a: ContainedTerm, b: ContainedTerm) -> Res<ContainedTerm> {
    Eq(lam_helper([a.clone().typed()?],II.ctn()?,"i",|[ty],_|{Ok(ty)})?,a,b).ctn()
}

/// principle of reflexivity
/// refl a : a ≡ a
pub fn refl(a: ContainedTerm) -> Res<ContainedTerm> {
    EqLam(lam_helper([a],II.ctn()?,"i",|[a],_|{Ok(a)})?).ctn()
}

/// A struct containing various theorems about equality
/// Axiom J: ∀ (T: Type) (a: T) (f: ∀ (b: T) (h: a ≡ b), Type), f a (λ i => a) → ∀ (b: T) (h: a ≡ b), f b h
/// Contractibility of singletons : ∀ (T: Type) (a: T) (s: Σ (b: T), (a ≡ b)), s = (a,refl)
#[derive(Clone)]
pub struct EqualTheorems {
    sig_contr: ContainedTerm,
    axiom_j: ContainedTerm,
}

impl EqualTheorems {
    /// Create a new instance based on two universe levels
    /// n controls the input universe level
    /// m controls the output universe level
    pub fn new(n: Natural, m: Natural) -> Res<EqualTheorems> {
        // target - based J
        // intermediate - contractibility of sigma
        
        let sig_contr = lam_helper_poly([],Universe(n).ctn()?,"ty",[n],|[],ty,[n]|{
            lam_helper_poly([ty.clone()],ty,"a",[n],|[ty],a,[n]|{
                let eqtyf = lam_helper([ty.clone(),a.clone()], ty.clone(), "b",|[ty,a],b|{
                    straight_eq(a, b)
                })?;
                // eqtyf = λ b: T, a ≡ b
                let pty = Sig(eqtyf.clone()).ctn()?;
                // pty : Σ b: T, a ≡ b
                lam_helper_poly([ty,a,pty.clone(),eqtyf],pty,"sig",[n],|[ty,a,pty,eqtyf],p,[n]|{
                    // SigInd(x) = ∀ T: Sig F -> Type, q: (∀ a: A, b: B a, T (sig F a b)), T x
                    // q{a: ty}: (∀ b: ty, p: a ≡ b, ((λ b: T, a ≡ b),a,refl) ≡ (_,b,p))
                    App(App(SigInd(p, n.suc()).ctn()?,lam_helper([eqtyf.clone(),a.clone()],pty,"p",|[eqtyf,a],p|{
                        straight_eq(Pair(eqtyf,a.clone(),refl(a)?).ctn()?, p)
                    })?).ctn()?,{
                        lam_helper([a,eqtyf],ty,"b",|[a,eqtyf],b|{
                            lam_helper([a,eqtyf.clone(),b.clone()],App(eqtyf,b).ctn()?,"p",|[a,eqtyf,b],p|{
                                EqLam(lam_helper([eqtyf,a,b,p],II.ctn()?,"i",|[eqtyf,a,b,p],i|{
                                    Pair(eqtyf,EqUw(p.clone(),i.clone()).ctn()?,EqLam(lam_helper([p,i],II.ctn()?,"j",|[p,i],j|{
                                        EqUw(p,And(i,j).ctn()?).ctn()
                                    })?).ctn()?).ctn()
                                })?).ctn()
                            })
                        })?
                    }).ctn()
                })
            })
        })?;

        // J : ∀ (T: Type) (a: T) (f: ∀ (b: T) (h: a ≡ b), Type), f a (λ i => a) → ∀ (b: T) (h: a ≡ b), f b h
        // J = λ (T: Type) (a: T) (f: ∀ (b: T) (h: a ≡ b), Type) (initial: f a (λ i => a)) (b: T) (h: a ≡ b) =>
        //          transp (λ i => f (h i) (λ j => h (i ∧ j))) initial

        let J = lam_helper_poly([], Universe(n).ctn()?, "T",[m],|[],ty,[m]|{
            lam_helper_poly([ty.clone()], ty, "a", [m], |[ty],a,[m]|{
                let fty = pi_helper_poly([a.clone()], ty.clone(), "b", [m], |[a],b,[m]|{
                    pi_helper_poly([], straight_eq(a, b)?, "h", [m], |[],h,[m]|{
                        Universe(m).ctn()
                    })
                })?;
                lam_helper_poly([a,ty], fty, "fam", (), |[a,ty],fam,()|{
                    lam_helper_poly([a.clone(),ty,fam.clone()], App(App(fam,a.clone()).ctn()?,refl(a)?).ctn()?, "init", (), |[a,ty,fam],init,()|{
                        lam_helper_poly([a,fam,init], ty, "b", (), |[a,fam,init],b,()|{
                            lam_helper_poly([fam,init], straight_eq(a, b)?, "h", (), |[fam,init],h,()|{
                                Transp(lam_helper([fam,h],II.ctn()?,"i",|[fam,h],i|{
                                    App(App(fam,EqUw(h.clone(),i.clone()).ctn()?).ctn()?,EqLam(lam_helper([h,i], II.ctn()?, "j", |[h,i],j|{
                                        EqUw(h,And(i,j).ctn()?).ctn()
                                    })?).ctn()?).ctn()
                                })?, init).ctn()
                            })
                        })
                    })
                })
            })
        })?;

        

        Ok(Self { sig_contr, axiom_j: J })
    }
}