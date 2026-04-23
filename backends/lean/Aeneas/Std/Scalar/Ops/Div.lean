import Aeneas.Std.Scalar.Core
import Aeneas.Std.Scalar.Misc
import Aeneas.Std.Scalar.Elab
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith ScalarElab WP

/-!
# Division: Definitions
-/

uscalar def «%S».div (x y : «%S») : Result «%S» :=
  if y.toBitVec != 0 then ok ⟨ BitVec.udiv x.toBitVec y.toBitVec ⟩ else fail divisionByZero

iscalar def «%S».div (x y : «%S») : Result «%S» :=
  if y.toInt != 0 then
    if ¬ (x.toInt = «%S».min && y.toInt = -1) then ok ⟨ BitVec.sdiv x.toBitVec y.toBitVec ⟩
    else fail integerOverflow
  else fail divisionByZero

class ResultDiv (α : Type u) where
  div : α → α → Result α

infixl:70 " /? " => ResultDiv.div

scalar instance : ResultDiv «%S» where
  div x y := «%S».div x y

scalar def «%S».try_div (x y : «%S») : Option «%S» :=
  Option.ofResult (x /? y)

/-!
# Sanity Checks
-/
/-!
The scalar division/modulo on signed machine integers 't'runcates towards 0, meaning it is
implemented by the `Int.tdiv`, `Int.tmod`, etc. definitions.
-/

namespace Tests
  -- Checking that the division over signed integers agrees with Rust
  #assert Int.tdiv 3 2 = 1
  #assert Int.tdiv (-3) 2 = -1
  #assert Int.tdiv 3 (-2) = -1
  #assert Int.tdiv (-3) (-2) = 1
  #assert Int.tdiv 7 3 = 2
  #assert Int.tdiv (-7) 3 = -2
  #assert Int.tdiv 7 (-3) = -2
  #assert Int.tdiv (-7) (-3) = 2

  -- Checking that the signed division over bit-vectors agrees with Rust
  private def toBitVec_sdiv (x y : Int) : Int :=
    (BitVec.sdiv (BitVec.ofInt 32 x) (BitVec.ofInt 32 y)).toInt

  #assert toBitVec_sdiv 3 2 = 1
  #assert toBitVec_sdiv (-3) 2 = -1
  #assert toBitVec_sdiv 3 (-2) = -1
  #assert toBitVec_sdiv (-3) (-2) = 1
  #assert toBitVec_sdiv 7 3 = 2
  #assert toBitVec_sdiv (-7) 3 = -2
  #assert toBitVec_sdiv 7 (-3) = -2
  #assert toBitVec_sdiv (-7) (-3) = 2
end Tests

/-!
# Division: Theorems
-/

/-!
Theorems with a specification which use integers and bit-vectors
-/


iscalar theorem Int.bmod_pow2_'S_numBits_minus_one :
  Int.bmod (2 ^ (%BitWidth - 1)) (2 ^ %BitWidth) = - 2 ^ (%BitWidth - 1) := by
  rw [Int.bmod]
  /- Just doing a case disjunction on the number of bits because
     those proofs are annoying -/
  cases System.Platform.numBits_eq <;> simp [*]

iscalar theorem «%S».neg_imp_neg_toInt_toNat_mod_pow_eq_neg_toInt (x : «%S»)
  (hNeg : x.toBitVec.toInt < 0) :
  ((-x.toInt).toNat : Int) % 2^%BitWidth = -(x.toInt : Int) := by
  have hmsb : x.toBitVec.msb = true := by
    have := @BitVec.msb_eq_toInt _ x.toBitVec
    simp only [hNeg] at this
    apply this
  have hx := @BitVec.toInt_eq_msb_cond _ x.toBitVec
  simp [hmsb] at hx
  have hBounds := x.hBounds
  have pow2Ineq : (2^(%BitWidth - 1) : Int) < 2^%BitWidth := by
    have := System.Platform.numBits_eq
    have : (0 : Int) < 2^(%BitWidth - 1) := by simp
    have : %BitWidth = %BitWidth - 1 + 1 := by omega
    conv => rhs; rw [this]
    rw [Int.pow_succ']
    omega
  have hyToNat : 2 ^ %BitWidth - x.toBitVec.toNat = (-x.toInt).toNat := by
    rw [hx]
    grind
  have hyValToNatMod : ((-x.toInt).toNat : Nat) % 2^%BitWidth = (-x.toInt).toNat := by
    have : ↑(-x.toInt).toNat < 2 ^ %BitWidth := by
      zify
      apply Int.lt_of_neg_lt_neg
      have : - (-x.toInt).toNat = x.toInt := by omega
      rw [this]; clear this
      have := x.hmin
      scalar_tac
    have := @Nat.mod_eq_of_lt (-x.toInt).toNat (2^%BitWidth) (by omega)
    apply this
  zify at hyValToNatMod
  rw [hyValToNatMod]
  omega

uscalar theorem «%S».div_bv_spec (x : «%S») {y : «%S»} (hnz : ↑y ≠ (0 : Nat)) :
  x /? y ⦃ z => (↑z : Nat) = ↑x / ↑y ∧ z.toBitVec = x.toBitVec / y.toBitVec ⦄ := by
  change @spec _ (x.div y) _
  apply exists_imp_spec
  have hzero' : y.toBitVec ≠ BitVec.ofNat _ 0 := by
    intro h
    zify at h
    simp_all
  simp [hzero', div]; rfl

set_option maxHeartbeats 600000 in
iscalar theorem «%S».div_bv_spec {x y : «%S»} (hnz : ↑y ≠ (0 : Int))
  (hNoOverflow : ¬ (x.toInt = «%S».min ∧ y.toInt = -1)) :
  ∃ z, x /? y = ok z ∧ (↑z : Int) = Int.tdiv ↑x ↑y ∧ z.toBitVec = BitVec.sdiv x.toBitVec y.toBitVec := by
  conv => congr; ext; lhs; simp only [ResultDiv.div]
  simp only [div, bne_iff_ne, ne_eq, hnz, not_false_eq_true, ↓reduceIte, Int.reduceNeg,
    Bool.and_eq_true, decide_eq_true_eq, hNoOverflow, ok.injEq, _root_.exists_eq_left', and_true]
  simp only [toInt]
  -- TODO: simplify the proof by using BitVec.toInt_srem

  simp only [BitVec.sdiv_eq, BitVec.udiv_eq, BitVec.udiv_def, BitVec.toNat_neg, toBitVec_toInt_eq]
  have pow2Ineq : (2^(%BitWidth - 1) : Int) < 2^%BitWidth := by
    have := System.Platform.numBits_eq
    have : (0 : Int) < 2^(%BitWidth - 1) := by simp only [Nat.ofNat_pos, pow_pos]
    have : %BitWidth = %BitWidth - 1 + 1 := by omega
    conv => rhs; rw [this]
    rw [Int.pow_succ']
    omega
  have hxBounds := x.hBounds
  have hyBounds := y.hBounds

  split

  . -- 0 ≤ x.toBitVec.toInt
    -- 0 ≤ y.toBitVec.toInt
    rw [@BitVec.toInt_ofNat' %BitWidth]
    simp only [Int.natCast_ediv]
    have hx : x.toBitVec.toNat = x.toBitVec.toInt := by
      have := @BitVec.toInt_eq_msb_cond _ x.toBitVec
      simp_all
    have hy : y.toBitVec.toNat = y.toBitVec.toInt := by
      have := @BitVec.toInt_eq_msb_cond _ y.toBitVec
      simp_all
    simp only [hx, toBitVec_toInt_eq, hy]
    simp only [toBitVec_toInt_eq] at hx hy
    have := @Int.tdiv_nonneg x.toInt y.toInt (by omega) (by omega)
    have : -2 ^ (%BitWidth - 1) ≤ 0 := by
      simp only [Left.neg_nonpos_iff, Nat.ofNat_nonneg, pow_nonneg]
    have : (x.toInt).tdiv y.toInt < 2 ^ (%BitWidth - 1) := by
      rw [Int.tdiv_eq_ediv]; split <;> try omega
      have := @Int.ediv_le_self x.toInt y.toInt (by omega)
      scalar_tac

    have hEq := bmod_pow_numBits_eq_of_lt (Int.tdiv x.toInt y.toInt) (by omega) (by omega)
    rw [← hEq]
    have htdiv : Int.tdiv x.toInt y.toInt = x.toInt / y.toInt := by
      rw [Int.tdiv_eq_ediv]
      have : 0 ≤ x.toInt := by omega
      simp only [this, true_or, ↓reduceIte, add_zero]
    rw [htdiv]

  . -- 0 ≤ x.toBitVec.toInt
    -- y.toBitVec.toInt < 0
    rename_i hxIneq hyIneq
    have hx := @BitVec.toInt_eq_msb_cond _ x.toBitVec
    simp only [toBitVec_toInt_eq, hxIneq, Bool.false_eq_true, ↓reduceIte] at hx
    have hy := @BitVec.toInt_eq_msb_cond _ y.toBitVec
    simp only [toBitVec_toInt_eq, hyIneq, ↓reduceIte, Nat.cast_pow, Nat.cast_ofNat] at hy
    have hyNeg : y.toInt < 0 := by
      have := @BitVec.msb_eq_toInt _ y.toBitVec
      simp_all
    have : -2 ^ (%BitWidth - 1) ≤ Int.tdiv x.toInt y.toInt := by
      have : Int.tdiv x.toInt (-y.toInt) ≤ 2^(%BitWidth - 1) := by
        rw [Int.tdiv_eq_ediv]
        have := @Int.ediv_le_self x.toInt (-y.toInt) (by omega)
        simp only [ne_eq, Int.reduceNeg, not_and, Int.ediv_neg, ge_iff_le] at *
        have := x.hmax
        scalar_tac
      replace this := Int.neg_le_neg this
      simp only [Int.tdiv_neg, neg_neg] at this
      apply this
    have hyToNat : 2 ^ %BitWidth - y.toBitVec.toNat = (-y.toInt).toNat := by
      rw [hy]
      simp only [neg_sub, Int.toNat_sub']
      norm_cast
    rw [BitVec.toInt_neg, @BitVec.toInt_ofNat' %BitWidth]
    simp only [Int.natCast_ediv, Int.natCast_emod, Nat.cast_pow, Nat.cast_ofNat]
    rw [hyToNat]
    have : ((-y.toInt).toNat : Int) % 2^%BitWidth = -(y.toInt : Int) := by
      apply neg_imp_neg_toInt_toNat_mod_pow_eq_neg_toInt
      simp only [toBitVec_toInt_eq]; omega
    rw [this]; clear this
    simp only [Int.ediv_neg]
    apply Eq.trans Int.bmod_neg_bmod _
    rw [neg_neg, ← hx]
    have : (x.toInt / y.toInt).bmod (2^%BitWidth) = x.toInt / y.toInt := by
      have : -2 ^ (%BitWidth - 1) ≤ x.toInt / ↑y := by
        apply Int.le_of_neg_le_neg
        have : - (x.toInt / y.toInt) = x.toInt / -y.toInt := by simp only [Int.ediv_neg]
        rw [this]; clear this
        have := @Int.ediv_le_self x.toInt (-y.toInt) (by omega)
        scalar_tac
      have : x.toInt / ↑y < 2 ^ (%BitWidth - 1) := by
        have : 0 < 2 ^ (%BitWidth - 1) := by simp only [Nat.ofNat_pos, pow_pos]
        have : x.toInt / y.toInt ≤ 0 := by apply Int.ediv_nonpos_of_nonneg_of_nonpos <;> omega
        scalar_tac
      have := bmod_pow_numBits_eq_of_lt (x.toInt / y.toInt) (by omega) (by omega)
      rw [this]

    rw [this]; clear this

    have : x.toInt.tdiv y.toInt = - (x.toInt.tdiv (-y.toInt)) := by simp only [Int.tdiv_neg, neg_neg]
    rw [this]
    have : x.toInt.tdiv (-y.toInt) = (x.toInt) / (-y.toInt) := by
      have := @Int.tdiv_eq_ediv x.toInt (-y.toInt)
      rw [this]
      split <;> omega
    rw [this]; clear this
    simp only [Int.ediv_neg, neg_neg]

  . -- x.toBitVec.toInt < 0
    -- 0 ≤ y.toBitVec.toInt
    rename_i hxIneq hyIneq
    have hx := @BitVec.toInt_eq_msb_cond _ x.toBitVec
    simp only [toBitVec_toInt_eq, hxIneq, ↓reduceIte, Nat.cast_pow, Nat.cast_ofNat] at hx
    have hy := @BitVec.toInt_eq_msb_cond _ y.toBitVec
    simp only [toBitVec_toInt_eq, hyIneq, Bool.false_eq_true, ↓reduceIte] at hy
    have hxNeg : x.toInt < 0 := by
      have := @BitVec.msb_eq_toInt _ x.toBitVec
      simp_all
    have hyPos : 0 ≤ y.toInt := by
      have := @BitVec.msb_eq_toInt _ y.toBitVec
      simp_all
    have : -2 ^ (%BitWidth - 1) ≤ x.toInt / y.toInt := by
      have := @Int.ediv_le_ediv (-2 ^ (%BitWidth - 1)) x.toInt y.toInt (by omega) (by scalar_tac)
      have := @Int.self_le_ediv x.toInt y.toInt (by omega) (by omega)
      scalar_tac
    have hxToNat : 2 ^ %BitWidth - x.toBitVec.toNat = (-x.toInt).toNat := by
      rw [hx]
      simp only [neg_sub, Int.toNat_sub']
      norm_cast
    rw [BitVec.toInt_neg, BitVec.toInt_ofNat']
    simp only [Int.natCast_ediv, Int.natCast_emod, Nat.cast_pow, Nat.cast_ofNat]

    unfold IScalarTy.numBits
    rw [hxToNat]
    have : ((-x.toInt).toNat : Int) % 2^%BitWidth = -(x.toInt : Int) := by
      apply neg_imp_neg_toInt_toNat_mod_pow_eq_neg_toInt
      simp only [toBitVec_toInt_eq]; omega
    rw [this]; clear this

    /- We have to treat separately the degenerate case where `x` touches the upper bound
       and `y = 1` -/
    dcases hxDivY : -x.toInt / y.toInt = 2^(%BitWidth - 1)
    . rw [← hy]
      rw [hxDivY]
      have ⟨ hx, hy ⟩ : x.toInt = - 2^(%BitWidth - 1) ∧ y.toInt = 1 := by
        have := @Int.le_div_eq_bound_imp_eq (-x.toInt) y.toInt (2^(%BitWidth - 1))
          (by omega) (by scalar_tac) (by omega) (by omega)
        omega
      simp only [hx, hy, Int.tdiv_one]

      have : Int.bmod (2 ^ (%BitWidth - 1)) (2 ^ %BitWidth) =
             - 2 ^ (%BitWidth - 1) :=
        Int.bmod_pow2_'S_numBits_minus_one
      rw [this]
      simp only [neg_neg]
      rw [this]
    . have : 0 ≤ (-x.toInt) / y.toInt := by
        apply Int.ediv_nonneg <;> omega
      have : -x.toInt / y.toInt < 2^(%BitWidth - 1) := by
        have : -x.toInt ≤ 2^(%BitWidth - 1) := by scalar_tac
        have := @Int.ediv_le_self (-x.toInt) y.toInt (by omega)
        omega
      rw [← hy]
      have : (-x.toInt / y.toInt).bmod (2 ^ %BitWidth) =
             (-x.toInt / y.toInt) := by
        apply bmod_pow_numBits_eq_of_lt _ (by omega) (by omega)
      rw [this]; clear this
      have : (-(-x.toInt / ↑y)).bmod (2 ^ %BitWidth) =
             (-(-x.toInt / ↑y)) := by
        apply bmod_pow_numBits_eq_of_lt _ (by omega) (by omega)
      rw [this]; clear this
      have : (-x.toInt) / y.toInt = (-x.toInt).tdiv y.toInt := by
        rw [Int.tdiv_eq_ediv]
        omega

      rw [this]; simp only [Int.neg_tdiv, neg_neg]

  . -- x.toBitVec.toInt < 0
    -- y.toBitVec.toInt < 0
    rename_i hxIneq hyIneq
    have hx := @BitVec.toInt_eq_msb_cond _ x.toBitVec
    simp only [toBitVec_toInt_eq, hxIneq, ↓reduceIte, Nat.cast_pow, Nat.cast_ofNat] at hx
    have hy := @BitVec.toInt_eq_msb_cond _ y.toBitVec
    simp only [toBitVec_toInt_eq, hyIneq, ↓reduceIte, Nat.cast_pow, Nat.cast_ofNat] at hy
    have hxNeg : x.toInt < 0 := by
      have := @BitVec.msb_eq_toInt _ x.toBitVec
      simp_all
    have hyNeg : y.toInt < 0 := by
      have := @BitVec.msb_eq_toInt _ y.toBitVec
      simp_all
    have hxToNat : 2 ^ %BitWidth - x.toBitVec.toNat = (-x.toInt).toNat := by
      rw [hx]
      simp only [neg_sub, Int.toNat_sub']
      norm_cast
    have hyToNat : 2 ^ %BitWidth - y.toBitVec.toNat = (-y.toInt).toNat := by
      rw [hy]
      simp only [neg_sub, Int.toNat_sub']
      norm_cast
    unfold IScalarTy.numBits
    rw [hxToNat, hyToNat]

    have : (-x.toInt).toNat % 2^%BitWidth = (-x.toInt).toNat := by
      apply Nat.mod_eq_of_lt
      scalar_tac
    rw [this]
    have : (-y.toInt).toNat % 2^%BitWidth = (-y.toInt).toNat := by
      apply Nat.mod_eq_of_lt
      scalar_tac
    rw [this]

    rw [BitVec.toInt_ofNat']

    /- We have to treat separately the degenerate case where `x` touches the lower bound
       and `y = -1`, because then `x / y` actually overflows -/
    have hxyInBouds : (-x.toInt) / (-y.toInt) ≠ 2^(%BitWidth - 1) := by
      -- We do the proof by contradiction
      intro hEq
      have hContra : x.toInt = - 2^(%BitWidth - 1) ∧ y.toInt = -1 := by
        have := @Int.le_div_eq_bound_imp_eq (-x.toInt) (-y.toInt) (2^(%BitWidth - 1))
          (by omega) (by scalar_tac) (by omega) (by omega)
        omega
      simp only [hContra, min, Int.reduceNeg, and_self, not_true_eq_false, numBits,
        IScalarTy.numBits] at hNoOverflow

    have : -(2 ^ (%BitWidth - 1) : Int) ≤ ↑((-x.toInt).toNat / (-y.toInt).toNat) := by
      have := @Int.ediv_nonneg (-x.toInt).toNat (-y.toInt).toNat (by omega) (by omega)
      have : -(2 ^ (%BitWidth - 1) : Int) ≤ 0 := by
        simp only [Left.neg_nonpos_iff, Nat.ofNat_nonneg, pow_nonneg]
      omega

    have : ((-x.toInt).toNat / (-y.toInt).toNat) < (2 ^ (%BitWidth - 1) : Int) := by
      -- First prove a ≤ bound
      have hIneq : ((-x.toInt).toNat / (-y.toInt).toNat) ≤ (2 ^ (%BitWidth - 1) : Int) := by
        have := @Int.ediv_le_self (-x.toInt).toNat (-y.toInt).toNat (by omega)
        scalar_tac
      -- Then use the hypothesis about the fact that we're not equal to the bound
      zify at hIneq
      have : (-x.toInt).toNat = -x.toInt := by omega
      rw [this] at hIneq; rw [this]
      have : (-y.toInt).toNat = -y.toInt := by omega
      rw [this] at hIneq; rw [this]
      omega
    have := bmod_pow_numBits_eq_of_lt ((-x.toInt).toNat / (-y.toInt).toNat : Nat) (by omega) (by omega)
    rw [this]

    zify; simp only [Int.ofNat_toNat]

    have : (-x.toInt) ⊔ 0 = -x.toInt := by omega
    simp only [this]; clear this
    have : -↑y ⊔ 0 = -y.toInt := by omega
    simp only [this]; clear this

    have : (-x.toInt) / (-y.toInt) = (-x.toInt).tdiv (-y.toInt) := by
      rw [Int.tdiv_eq_ediv]; omega
    rw [this]
    simp only [Int.tdiv_neg, Int.neg_tdiv, neg_neg]

/-!
Theorems with a specification which only use integers
-/

uscalar @[step] theorem «%S».div_spec (x : «%S») {y : «%S»} (hnz : ↑y ≠ (0 : Nat)) :
  (x /? y) ⦃ z => (↑z : Nat) = ↑x / ↑y ⦄ :=
  spec_mono («%S».div_bv_spec x hnz) (fun _ h => h.1)

iscalar @[step] theorem «%S».div_spec {x y : «%S»} (hnz : ↑y ≠ (0 : Int))
  (hNoOverflow : ¬ (x.toInt = «%S».min ∧ y.toInt = -1)) :
  (x /? y) ⦃ z => (↑z : Int) = Int.tdiv ↑x ↑y ⦄ := by
  have ⟨z, hz⟩ := «%S».div_bv_spec hnz hNoOverflow
  exact exists_imp_spec ⟨z, by simp [hz]⟩

end Aeneas.Std
