pub type Word = u64;

#[derive(Debug, Copy, Clone)]
pub struct ConstChoice(Word);

#[derive(Copy, Clone, Default, Hash)]
pub struct Limb(pub Word);

impl Limb {
    /// The value `0`.
    pub const ZERO: Self = Limb(0);
}

impl ConstChoice {
    pub(crate) const fn if_true_word(&self, x: Word) -> Word {
        unimplemented!()
    }
}

pub struct Uint<const LIMBS: usize> {
    /// Inner limb array. Stored from least significant to most significant.
    pub(crate) limbs: [Limb; LIMBS],
}

impl<const LIMBS: usize> Uint<LIMBS> {
    /// Computes `-a mod p`.
    /// Assumes `self` is in `[0, p)`.
    pub const fn neg_mod(&self, p: &Self) -> Self {
        let z = self.is_nonzero();
        let mut ret = p.sbb(self, Limb::ZERO).0;
        let mut i = 0;
        while i < LIMBS {
            // Set ret to 0 if the original value was 0, in which
            // case ret would be p.
            ret.limbs[i].0 = z.if_true_word(ret.limbs[i].0);
            i += 1;
        }
        ret
    }

    pub const fn sbb(&self, rhs: &Self, mut borrow: Limb) -> (Self, Limb) {
        unimplemented!()
    }

    pub(crate) const fn is_nonzero(&self) -> ConstChoice {
        unimplemented!()
    }
}

fn main(){}
