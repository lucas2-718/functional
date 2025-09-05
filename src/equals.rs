use crate::{ctypes::{ContainedTerm, Natural, Res, Term::*, check, lam_helper, lam_helper_poly}, display::{AliasMap, pretty_print_base}};

fn straight_eq(a: ContainedTerm, b: ContainedTerm) -> Res<ContainedTerm> {
    Eq(lam_helper([a.clone().typed()?],II.ctn()?,|[ty],_|{Ok(ty)})?,a,b).ctn()
}

fn refl(a: ContainedTerm) -> Res<ContainedTerm> {
    EqLam(lam_helper([a],II.ctn()?,|[a],_|{Ok(a)})?).ctn()
}

pub fn run(n: Natural) -> Res<()> {
    // target - based J
    // intermediate - contractibility of sigma
    
    let sig_contr = lam_helper_poly([],Universe(n).ctn()?,[n],|[],ty,[n]|{
        lam_helper_poly([ty.clone()],ty,[n],|[ty],a,[n]|{
            let eqtyf = lam_helper([ty.clone(),a.clone()], ty.clone(), |[ty,a],b|{
                straight_eq(a, b)
            })?;
            // eqtyf = λ b: T, a ≡ b
            let pty = Sig(eqtyf.clone()).ctn()?;
            // pty : Σ b: T, a ≡ b
            lam_helper_poly([ty,a,pty.clone(),eqtyf],pty,[n],|[ty,a,pty,eqtyf],p,[n]|{
                // SigInd(x) = ∀ T: Sig F -> Type, q: (∀ a: A, b: B a, T (sig F a b)), T x
                // q{a: ty}: (∀ b: ty, p: a ≡ b, ((λ b: T, a ≡ b),a,refl) ≡ (_,b,p))
                App(App(SigInd(p, n.suc()).ctn()?,lam_helper([eqtyf.clone(),a.clone()],pty,|[eqtyf,a],p|{
                    straight_eq(Pair(eqtyf,a.clone(),refl(a)?).ctn()?, p)
                })?).ctn()?,{
                    lam_helper([a,eqtyf],ty,|[a,eqtyf],b|{
                        lam_helper([a,eqtyf.clone(),b.clone()],App(eqtyf,b).ctn()?,|[a,eqtyf,b],p|{
                            EqLam(lam_helper([eqtyf,a,b,p],II.ctn()?,|[eqtyf,a,b,p],i|{
                                Pair(eqtyf,EqUw(p.clone(),i.clone()).ctn()?,EqLam(lam_helper([p,i],II.ctn()?,|[p,i],j|{
                                    EqUw(p,And(i,j).ctn()?).ctn()
                                })?).ctn()?).ctn()
                            })?).ctn()
                        })
                    })?
                }).ctn()
            })
        })
    })?;

    //check(sig_contr);
    println!("{}",pretty_print_base(sig_contr, &AliasMap::new()));
    Ok(())
}