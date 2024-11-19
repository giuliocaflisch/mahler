/-

Authors: Giulio Caflisch, David Loeffler
-/
import Mahler.fwdDiff

variable {R : Type*} [CommRing R]
variable {M : AddSubmonoid R}
variable {h : M} [H : Fact (IsUnit (h : R))]

noncomputable def discDeriv (f : M → R) : M → R :=
  fun x ↦ (fwdDiff h f x) * (H.out.unit.inv : R)
