import Lean
import Egg
import Mathlib.Algebra.Ring.Defs
open Lean Meta Elab Tactic Term

macro "egg_ring" : tactic => `(tactic|
  egg (config := { genGoalTcSpec := true }) [
    AddSemigroup.add_assoc,
    AddMonoid.zero_add,
    AddMonoid.add_zero,
    AddMonoid.nsmul_zero,
    AddMonoid.nsmul_succ,
    AddCommMonoid.add_comm,
    NonUnitalNonAssocSemiring.left_distrib,
    NonUnitalNonAssocSemiring.right_distrib,
    NonUnitalNonAssocSemiring.zero_mul,
    NonUnitalNonAssocSemiring.mul_zero,
    NonUnitalSemiring.mul_assoc,
    Semiring.one_mul,
    Semiring.mul_one,
    Semiring.natCast_zero,
    Semiring.natCast_succ,
    Semiring.npow_zero,
    Semiring.npow_succ,
    Ring.sub_eq_add_neg,
    Ring.zsmul_zero',
    Ring.zsmul_succ',
    Ring.zsmul_neg',
    Ring.add_left_neg,
    Ring.intCast_ofNat,
    Ring.intCast_negSucc,
    CommRing.mul_comm
  ]
)
