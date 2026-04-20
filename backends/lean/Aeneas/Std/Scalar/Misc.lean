import Aeneas.Std.Scalar.Core
import Aeneas.Tactic.Solver.ScalarTac
import Mathlib.Data.BitVec

namespace Aeneas.Std

open Result Error Arith

/-- Important theorem to reason with `Int.bmod` in the proofs about `IScalar` -/
theorem bmod_pow_numBits_eq_of_lt (ty : IScalarTy) (x : Int)
  (h0 : - 2 ^ (ty.numBits-1) ≤ x) (h1 : x < 2 ^ (ty.numBits -1)) :
  Int.bmod x (2^ty.numBits) = x := by
  have := ty.numBits_nonzero
  have hEq : ty.numBits - 1 + 1 = ty.numBits := by omega
  have := Int.bmod_pow2_eq_of_inBounds (ty.numBits-1) x (by omega) (by omega)
  simp [hEq] at this
  apply this

/-- We need this lemma to prove the theorems about division and remainder -/
theorem IScalar.neg_imp_toNat_neg_eq_neg_toInt {ty} (x : IScalar ty) (hNeg : x.toInt < 0):
  (-(IScalar.toBitVec x)).toNat = -(IScalar.toBitVec x).toInt := by
  have hmsb : (IScalar.toBitVec x).msb = true := by
    rw [BitVec.msb_eq_toInt, decide_eq_true_eq]
    cases ty <;> simp_all [IScalar.toInt, IScalar.toBitVec]
  have hx := @BitVec.toInt_eq_msb_cond _ (IScalar.toBitVec x)
  simp [hmsb] at hx

  have hxNeg : x.toInt < 0 := by
    have := @BitVec.msb_eq_toInt _ (IScalar.toBitVec x)
    simp_all

  conv => lhs; simp only [Neg.neg, BitVec.neg]
  simp only [BitVec.toInt_eq_toNat_bmod]

  have hxToNatMod : ((IScalar.toBitVec x).toNat : Int) % 2^ty.numBits = (IScalar.toBitVec x).toNat := by
    apply Int.emod_eq_of_lt <;> omega

  have hPow : (2 ^ ty.numBits + 1 : Int) / 2  = 2^(ty.numBits - 1) := by
    have : ty.numBits = ty.numBits - 1 + 1 := by
      have := ty.numBits_nonzero
      omega
    conv => lhs; rw [this]
    rw [Int.pow_succ']
    rw [Int.add_ediv_of_dvd_left] <;> simp

  have : ¬ (((IScalar.toBitVec x).toNat : Int) % ↑(2 ^ ty.numBits : Nat) < (↑(2 ^ ty.numBits : Nat) + 1) / 2) := by
    have hIneq := @BitVec.msb_eq_toNat _ (IScalar.toBitVec x)
    rw [hmsb] at hIneq
    simp at hIneq
    simp
    rw [hPow]

    rw [hxToNatMod]
    zify at hIneq
    omega
  rw [Int.bmod_def]
  simp only [this]
  simp
  have : (2 ^ ty.numBits - (IScalar.toBitVec x).toNat : Nat) % (2 ^ ty.numBits : Int) =
         (2^ty.numBits - (IScalar.toBitVec x).toNat : Nat) := by
    apply Int.emod_eq_of_lt
    . omega
    . have := x.hBounds
      simp only [IScalar.toInt] at *
      have : (2 ^ ty.numBits - (IScalar.toBitVec x).toNat : Nat) = (2 ^ ty.numBits - (IScalar.toBitVec x).toNat : Int) := by
        have : (2 ^ ty.numBits : Nat) = (2 ^ ty.numBits : Int) := by simp
        omega
      rw [this]
      have : (IScalar.toBitVec x).toNat > 0 := by
        by_contra
        have hxz : (IScalar.toBitVec x).toNat = 0 := by omega
        have : (IScalar.toBitVec x).toInt = 0 := by
          simp only [BitVec.toInt_eq_toNat_bmod, Int.bmod_def, hxz]
          simp [hPow]
        omega
      omega
  rw [this]; clear this
  rw [hxToNatMod]

  have : (2 ^ ty.numBits : Nat) = (2 ^ ty.numBits : Int) := by simp
  omega

/-!
# Misc Theorems
-/

@[simp] theorem UScalar.exists_eq_left {p : UScalar ty → Prop} {a' : UScalar ty} :
  (∃ (a : UScalar ty), a.toNat = a'.toNat ∧ p a) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, h, hp ⟩ := h
    have ha : a = a' := UScalar.toNat_eq_imp a a' h
    subst ha; exact hp
  . exact ⟨a', rfl, h⟩

@[simp] theorem IScalar.exists_eq_left {p : IScalar ty → Prop} {a' : IScalar ty} :
  (∃ (a : IScalar ty), a.toInt = a'.toInt ∧ p a) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, h, hp ⟩ := h
    have ha : a = a' := IScalar.toInt_eq_imp a a' h
    subst ha; exact hp
  . exact ⟨a', rfl, h⟩

@[simp] theorem UScalar.exists_eq_left' {p : UScalar ty → Prop} {a' : UScalar ty} :
  (∃ (a : UScalar ty), a'.toNat = a.toNat ∧ p a) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, h, hp ⟩ := h
    have ha : a = a' := UScalar.toNat_eq_imp a a' h.symm
    subst ha; exact hp
  . exact ⟨a', rfl, h⟩

@[simp] theorem IScalar.exists_eq_left' {p : IScalar ty → Prop} {a' : IScalar ty} :
  (∃ (a : IScalar ty), a'.toInt = a.toInt ∧ p a) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, h, hp ⟩ := h
    have ha : a = a' := IScalar.toInt_eq_imp a a' h.symm
    subst ha; exact hp
  . exact ⟨a', rfl, h⟩

@[simp] theorem UScalar.exists_eq_right {p : UScalar ty → Prop} {a' : UScalar ty} :
  (∃ (a : UScalar ty), p a ∧ a.toNat = a'.toNat) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, hp, h ⟩ := h
    have ha : a = a' := UScalar.toNat_eq_imp a a' h
    subst ha; exact hp
  . exact ⟨a', h, rfl⟩

@[simp] theorem IScalar.exists_eq_right {p : IScalar ty → Prop} {a' : IScalar ty} :
  (∃ (a : IScalar ty), p a ∧ a.toInt = a'.toInt) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, hp, h ⟩ := h
    have ha : a = a' := IScalar.toInt_eq_imp a a' h
    subst ha; exact hp
  . exact ⟨a', h, rfl⟩

@[simp] theorem UScalar.exists_eq_right' {p : UScalar ty → Prop} {a' : UScalar ty} :
  (∃ (a : UScalar ty), p a ∧ a'.toNat = a.toNat) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, hp, h ⟩ := h
    have ha : a = a' := UScalar.toNat_eq_imp a a' h.symm
    subst ha; exact hp
  . exact ⟨a', h, rfl⟩

@[simp] theorem IScalar.exists_eq_right' {p : IScalar ty → Prop} {a' : IScalar ty} :
  (∃ (a : IScalar ty), p a ∧ a'.toInt = a.toInt) ↔ p a' := by
  constructor <;> intro h
  . replace ⟨ a, hp, h ⟩ := h
    have ha : a = a' := IScalar.toInt_eq_imp a a' h.symm
    subst ha; exact hp
  . exact ⟨a', h, rfl⟩

@[simp] theorem UScalar.exists_eq {a' : UScalar ty} : ∃ (a : UScalar ty), a.toNat = a'.toNat := by exists a'
@[simp] theorem UScalar.exists_eq' {a' : UScalar ty} : ∃ (a : UScalar ty), a'.toNat = a.toNat := by exists a'
@[simp] theorem IScalar.exists_eq {a' : IScalar ty} : ∃ (a : IScalar ty), a.toInt = a'.toInt := by exists a'
@[simp] theorem IScalar.exists_eq' {a' : IScalar ty} : ∃ (a : IScalar ty), a'.toInt = a.toInt := by exists a'

/-!
# Equalities and simplification lemmas
-/

theorem UScalar.ofNatCore_bv_lt_equiv {ty} (x y : Nat) (hx) (hy) :
  (UScalar.toBitVec (@UScalar.ofNatCore ty x hx)) < (UScalar.toBitVec (@UScalar.ofNatCore ty y hy)) ↔ x < y := by
  simp only [UScalar.ofNatCore, UScalar.toBitVec]
  cases ty <;> simp [BitVec.lt_ofFin]

@[simp, scalar_tac_simps] theorem U8.val_mod_size_eq (x : U8) : x.toNat % U8.size = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U8.val_mod_size_eq' (x : U8) : x.toNat % 256 = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U16.val_mod_size_eq (x : U16) : x.toNat % U16.size = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U16.val_mod_size_eq' (x : U16) : x.toNat % 65536 = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U32.val_mod_size_eq (x : U32) : x.toNat % U32.size = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U32.val_mod_size_eq' (x : U32) : x.toNat % 4294967296 = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U64.val_mod_size_eq (x : U64) : x.toNat % U64.size = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U64.val_mod_size_eq' (x : U64) : x.toNat % 18446744073709551616 = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U128.val_mod_size_eq (x : U128) : x.toNat % U128.size = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U128.val_mod_size_eq' (x : U128) : x.toNat % 340282366920938463463374607431768211456 = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem Usize.val_mod_size_eq (x : Usize) : x.toNat % Usize.size = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U8.val_mod_max_eq (x : U8) : x.toNat % (U8.max + 1) = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U16.val_mod_max_eq (x : U16) : x.toNat % (U16.max + 1) = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U32.val_mod_max_eq (x : U32) : x.toNat % (U32.max + 1) = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U64.val_mod_max_eq (x : U64) : x.toNat % (U64.max + 1) = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem U128.val_mod_max_eq (x : U128) : x.toNat % (U128.max + 1) = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem Usize.val_mod_max_eq (x : Usize) : x.toNat % (Usize.max + 1) = x.toNat := by
  apply Nat.mod_eq_of_lt; scalar_tac

@[simp, scalar_tac_simps] theorem I8.val_mod_size_eq (x : I8) : Int.bmod x.toInt I8.size = x.toInt := by
  simp [size]; apply Int.bmod_pow2_eq_of_inBounds' <;> scalar_tac

@[simp, scalar_tac_simps] theorem I8.val_mod_size_eq' (x : I8) : Int.bmod x.toInt 256 = x.toInt := by
  simp

@[simp, scalar_tac_simps] theorem I16.val_mod_size_eq (x : I16) : Int.bmod x.toInt I16.size = x.toInt := by
  simp [size]; apply Int.bmod_pow2_eq_of_inBounds' <;> scalar_tac

@[simp, scalar_tac_simps] theorem I16.val_mod_size_eq' (x : I16) : Int.bmod x.toInt 65536 = x.toInt := by
  simp

@[simp, scalar_tac_simps] theorem I32.val_mod_size_eq (x : I32) : Int.bmod x.toInt I32.size = x.toInt := by
  simp [size]; apply Int.bmod_pow2_eq_of_inBounds' <;> scalar_tac

@[simp, scalar_tac_simps] theorem I32.val_mod_size_eq' (x : I32) : Int.bmod x.toInt 4294967296 = x.toInt := by
  simp

@[simp, scalar_tac_simps] theorem I64.val_mod_size_eq (x : I64) : Int.bmod x.toInt I64.size = x.toInt := by
  simp [size]; apply Int.bmod_pow2_eq_of_inBounds' <;> scalar_tac

@[simp, scalar_tac_simps] theorem I64.val_mod_size_eq' (x : I64) : Int.bmod x.toInt 18446744073709551616 = x.toInt := by
  simp

@[simp, scalar_tac_simps] theorem I128.val_mod_size_eq (x : I128) : Int.bmod x.toInt I128.size = x.toInt := by
  simp [size]; apply Int.bmod_pow2_eq_of_inBounds' <;> scalar_tac

@[simp, scalar_tac_simps] theorem I128.val_mod_size_eq' (x : I128) : Int.bmod x.toInt 340282366920938463463374607431768211456 = x.toInt := by
  have h := val_mod_size_eq x
  simp only [I128.size, I128.numBits, IScalarTy.numBits] at h
  norm_num at h
  exact h

@[simp, scalar_tac_simps] theorem Isize.val_mod_size_eq (x : Isize) : Int.bmod x.toInt Isize.size = x.toInt := by
  simp [size]; apply Int.bmod_pow2_eq_of_inBounds' <;> try scalar_tac
  simp [numBits]; cases System.Platform.numBits_eq <;> simp [*]

@[simp] theorem U8.val_max_zero_eq (x : U8) : x.toNat ⊔ 0 = x.toNat := by scalar_tac
@[simp] theorem U16.val_max_zero_eq (x : U16) : x.toNat ⊔ 0 = x.toNat := by scalar_tac
@[simp] theorem U32.val_max_zero_eq (x : U32) : x.toNat ⊔ 0 = x.toNat := by scalar_tac
@[simp] theorem U64.val_max_zero_eq (x : U64) : x.toNat ⊔ 0 = x.toNat := by scalar_tac
@[simp] theorem U128.val_max_zero_eq (x : U128) : x.toNat ⊔ 0 = x.toNat := by scalar_tac
@[simp] theorem Usize.val_max_zero_eq (x : Usize) : x.toNat ⊔ 0 = x.toNat := by scalar_tac


end Aeneas.Std
