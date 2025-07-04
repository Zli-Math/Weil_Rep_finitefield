import Mathlib

import WeilRepFinitefield.Compute
import WeilRepFinitefield.QuadForm

section Orthogonal
variable {R : Type*} [CommSemiring R]  {M : Type*} [AddCommMonoid M]
[Module R M]

abbrev QuadraticForm.O (Q : QuadraticForm R M) :=
  {σ : M ≃ₗ[R] M // ∀ v : M, Q (σ v) = Q v}

end Orthogonal

namespace Compute.test


local notation "F" => (ZMod 2)

local notation "GL2" => ((Fin 2) → F) ≃ₗ[F] ((Fin 2) → F)

abbrev Q : QuadForm F 2 := !#[![0],![1,0]]
abbrev QQ := Q.toQuadraticForm

#synth Repr QQ.O

def mm : QQ.O := ⟨LinearEquiv.toGL'.symm ⟨!![0, 1; 1, 0],(by decide)⟩,by decide⟩

#check mm.2
#eval! FinEnum.toList QQ.O

abbrev Q' : QuadForm F 2 := !#[![1],![1,1]]
abbrev QQ' := Q'.toQuadraticForm

#synth Repr QQ'.O

def mm' : QQ'.O := ⟨LinearEquiv.toGL'.symm ⟨!![0, 1; 1, 0],by decide⟩,by decide⟩

#eval! FinEnum.toList QQ'.O


end Compute.test


section Quadratic_Form

open Heisenberg



variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V][Module K V]
variable (B : V → V → K )[bilinearB : IsBilinear B]



def form ( f: V → K) : ( V →  V →  K ) := fun x => (fun y => f (x + y) - f (x) - f (y))

@[ext]
class Quadraticform (f : V → K) where
bilinear : IsBilinear (form f)
sq_smul : ∀ (t : K) v , f ( t • v ) = t^2 * f (v)


@[ext]
class addQuadraticform (f : V → K)  where
Quadf : Quadraticform f
additive : ∀ a b , f (a + b) = f (a) + f (b)



variable (f : V → K )[Quadraticform f]


class NonDegenerate (B : V → V → K) where
  nondeg : ∀ v , (∀ w , B v w =0) → v = 0


def isNonDegenerate (B : V → V → K) := ∀ v , (∀ w , B v w =0) → v = 0

omit [Module K V] in
lemma NonDegenerate.isNonDegenerate (B : V → V → K) [h : NonDegenerate B] : isNonDegenerate B := h.nondeg


def alternatingform (B : V → V → K) : (V → V → K )  := fun v => (fun w => B v w - B w v)


abbrev C : Subgroup (Heisenberg B) := Subgroup.center _

abbrev SubK : Subgroup (Heisenberg B) where
  carrier := { a | a.1 = 0 }
  mul_mem' := by
    intro a b ha hb
    simp_all
    rw [mul_def]
    simp [ha , hb]
  one_mem' := by
    simp
  inv_mem' := by
    intro x h
    simp_all
    simp [inv_def , h]


--Proposition 1.4
theorem centralextension : (SubK B).carrier ⊆ (C B).carrier := by
  intro x h
  simp [SubK] at h
  rw [Subgroup.mem_carrier]
  rw [Subgroup.mem_center_iff]
  intro y
  repeat rw [mul_def]
  simp [add_comm , h]
--Subgroup.subgroupOf

theorem center_is_K_of_nondegenerateB [hnd: NonDegenerate (alternatingform B) ] : (SubK B) = (C B) := by
  have nondege : isNonDegenerate (alternatingform B) := NonDegenerate.isNonDegenerate _
  ext x
  constructor
  apply centralextension
  intro h
  simp [SubK , C] at h ⊢
  rw [Subgroup.mem_center_iff] at h
  simp_rw [mul_def] at h
  simp [add_comm] at h
  simp [isNonDegenerate, alternatingform] at nondege
  specialize nondege x.1
  exact nondege (by convert h using 1; simp [sub_eq_zero] ; tauto)

end Quadratic_Form
