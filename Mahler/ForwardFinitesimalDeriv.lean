/-

Authors: Giulio Caflisch, David Loeffler
-/
import Mahler.ForwardDiff

variable {R : Type*} [CommRing R]
variable {M : AddSubmonoid R}
variable (h : M) [H : Fact (IsUnit (h : R))]

noncomputable def fwdFinDeriv (f : M → R) : M → R :=
  fun x ↦ (fwdDiff h f x) * (H.out.unit.inv : R)

theorem fwdFinDeriv_iter_fwdDiff (f : M → R) (n : ℕ) :
    (fwdFinDeriv h)^[n] f = fun x ↦ ((fwdDiff h)^[n] f x) * (H.out.unit.inv : R)^n := by
  revert f
  induction' n with n hn
  · simp only [Function.iterate_zero, id_eq, Units.inv_eq_val_inv, pow_zero, mul_one, implies_true]
  · intro f
    ext x
    simp only [Function.iterate_succ_apply', hn, fwdFinDeriv, fwdDiff, ← sub_mul, mul_assoc, ← pow_succ]
