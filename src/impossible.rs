use crate::{ctypes::{ContainedTerm, ErrorType, Res, Scopeless, Term::*, lam_helper, lam_helper_poly}, equals::straight_eq};

/// Basic data about the type with no inhabitants, False
/// False is internally represented by 0 = 1, so any value of that may be used as a value of false
#[derive(Clone)]
pub struct FalseData {
    /// The False type that has no inhabitants and indicates logical impossibility
    pub false_type: ContainedTerm,
}

impl Scopeless for FalseData {}

impl FalseData {
    /// Create an instance of FalseData
    pub fn new() -> Res<Self> {
        Ok(Self {
            false_type : straight_eq(Zero.ctn()?,Succ(Zero.ctn()?).ctn()?)?
        })
    }
    /// Given a logically impossible term, make a term of any type via transport
    pub fn exfalso(&self, target: ContainedTerm) -> Res<ContainedTerm> {
        match target.clone().typed()?.pop() {
            Universe(n) => {
                let other: ContainedTerm = if (n==0u8.into()) {
                    Zero.ctn()?
                } else {
                    if (n==1u8.into()) {
                        Nat.ctn()?
                    } else {
                        Universe(n.pred().pred()).ctn()?
                    }
                };
                let othertype = other.clone().typed()?;
                let exfalso: ContainedTerm = lam_helper_poly([othertype,target,other], self.false_type.clone(), "hyp", [n],|[othertype,target,other],hyp,[n]|{
                    // Using the false equality, construct an equality between two types
                    let family = lam_helper_poly([othertype,target,hyp], II.ctn()?, "i", [n],|[othertype,target,hyp],i,[n]|{
                        let number = EqUw(hyp, i).ctn()?;
                        App(App(App(NatInd(number, n.suc()).ctn()?,Lam(Nat.ctn()?,Universe(n).ctn()?,"_".into()).ctn()?).ctn()?,othertype).ctn()?,lam_helper_poly([target], Nat.ctn()?, "_", [n],|[target],_,[n]|{
                            lam_helper([target], Universe(n).ctn()?, "_", |[target],_|{
                                Ok(target)
                            })
                        })?).ctn()
                    })?;

                    // then transport a known value in one type to the other arbitrary type, completing the exfalso
                    let transport = Transp(family, other).ctn()?;
                    
                    Ok(transport)
                })?;
                
                Ok(exfalso)
            }
            _ => Err(ErrorType::new("target is not a type!".into()))
        }
    }
}