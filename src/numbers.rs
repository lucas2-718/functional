
use crate::ctypes::{ContainedTerm, Res, Term::*};

#[derive(Debug)]
pub struct Numbers {
    add: ContainedTerm,
    multiply: ContainedTerm,
}

impl Numbers {
    fn new_internal() -> Res<Self> {

        let successor_post = Lam(Nat.ctn()?,Lam(Pi(Nat.ctn()?,Nat.ctn()?).ctn()?,Lam(Nat.ctn()?,Succ(App(DeBrujin(1u8.into(), Pi(Nat.ctn()?,Nat.ctn()?).ctn()?).ctn()?,DeBrujin(0u8.into(), Nat.ctn()?).ctn()?).ctn()?).ctn()?).ctn()?).ctn()?).ctn()?;
        let id = Lam(Nat.ctn()?,DeBrujin(0u8.into(), Nat.ctn()?).ctn()?).ctn()?;

        let repeat_arg_ty = Pi(Nat.ctn()?,Pi(Pi(Nat.ctn()?,Nat.ctn()?).ctn()?,Pi(Nat.ctn()?,Nat.ctn()?).ctn()?).ctn()?).ctn()?;

        let repeat = 
        Lam(repeat_arg_ty.clone(),
            Lam(Nat.ctn()?,
                App(App(App(NatInd(DeBrujin(0u8.into(), Nat.ctn()?).ctn()?,0u8.into()).ctn()?,Lam(Nat.ctn()?,
                    Pi(Nat.ctn()?,Nat.ctn()?).ctn()?
                ).ctn()?).ctn()?,id.clone()).ctn()?,DeBrujin(1u8.into(), repeat_arg_ty.clone()).ctn()?).ctn()?
            ).ctn()?
        ).ctn()?;
        
        
        let add = App(repeat.clone(),successor_post).ctn()?;

        let add_to = Lam(Nat.ctn()?,Lam(Pi(Nat.ctn()?,Nat.ctn()?).ctn()?,Lam(Nat.ctn()?,App(App(add.clone(),DeBrujin(2u8.into(), Nat.ctn()?).ctn()?).ctn()?,App(DeBrujin(1u8.into(), Pi(Nat.ctn()?,Nat.ctn()?).ctn()?).ctn()?,DeBrujin(0u8.into(), Nat.ctn()?).ctn()?).ctn()?).ctn()?).ctn()?).ctn()?).ctn()?;

        let multiply = Lam(Nat.ctn()?,App(repeat.clone(),Lam(Nat.ctn()?,App(add_to.clone(),DeBrujin(1u8.into(), Nat.ctn()?).ctn()?).ctn()?).ctn()?).ctn()?).ctn()?;
        
        Ok(Self{add,multiply})
    }
    pub fn new() -> Self {
        Self::new_internal().unwrap()
    }
}