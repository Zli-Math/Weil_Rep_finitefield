import Mathlib
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

section Heisenberggrp
variable (K : Type*) [Field K][CharP K 2](V : Type*) [AddCommGroup V]


@[ext]
structure heisenbergele (B : V × V → K) where
x : V
y : K


class Biform where
B :V × V → K


class IsBilinear (B : V × V → K) where
llinear : ∀ r w v , B (r + w , v) =  B ( r  , v) + B ( w , v)
rlinear : ∀ r w v , B ( w , r + v) = B ( w , r ) + B ( w, v )

namespace heisenberg


variable ( B : V × V → K ) [bilinearB : IsBilinear K V B]


--the operator on Heisenberg group
def hprod  (a b : heisenbergele K V B)  : heisenbergele K V B:=
⟨ a.x + b.x , a.y + b.y + B ( a.x , b.x ) ⟩

instance : Add (heisenbergele K V B) where
   add := hprod K V B

lemma add_def (a b : heisenbergele K V B) : a + b = hprod K V B a b := rfl


instance : Neg  ( heisenbergele K V B) where
   neg := fun a => ⟨ -a.x , -a.y + B ( a.x , a.x)⟩

instance : HMul (heisenbergele K V B) (heisenbergele K V B) (heisenbergele K V B) where
  hMul := hprod K V B

instance : Zero (heisenbergele K V B) := ⟨0 , 0⟩

lemma zero_def : (0 : heisenbergele K V B ) = ⟨0, 0⟩ := rfl


lemma hprod_assoc (a b c : heisenbergele K V B) : a + b +c = a+ ( b + c ) := by
    simp [add_def ,hprod , add_assoc]
    simp [bilinearB.llinear , bilinearB.rlinear ]
    ring


lemma Blzero (b:  V) : B ( 0 , b ) = 0 := by
  have h : B (0, b) = B (0, b) := by rfl
  nth_rewrite 1 [←zero_add 0] at h
  rw [bilinearB.llinear] at h
  simp at h
  exact h

lemma Brzero (b:  V) : B ( b , 0 ) = 0 := by
  have h : B ( b , 0 ) = B ( b , 0 ) := by rfl
  nth_rewrite 1 [←zero_add 0] at h
  rw [bilinearB.rlinear] at h
  simp at h
  exact h



lemma hzero_add (a : heisenbergele K V B ) : 0 + a = a := by
    simp [add_def , hprod, zero_def]
    ext <;> simp
    rw [ Blzero K V B a.x ]

lemma add_hzero ( a : heisenbergele K V B ) :  a + 0 = a := by
    simp [add_def, hprod, zero_def]
    ext <;> simp
    rw [Brzero K V B a.x ]



instance Heisenberggrp : AddGroup (heisenbergele K V B) where
  add := (· + ·)
  zero := 0
  neg := fun a => ⟨-a.x, -a.y + B (a.x , a.x) ⟩
  add_assoc := hprod_assoc K V B
  zero_add := hzero_add K V B
  add_zero := add_hzero K V B
  neg_add_cancel := by
    intro a
    simp [add_def, hprod]
    simp [ ← bilinearB.llinear , Blzero]
    rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

end heisenberg
