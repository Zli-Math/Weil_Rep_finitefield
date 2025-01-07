import Mathlib
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

section HeisenbergGroup

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
variable (B : V → V → K)


abbrev Heisenberg (B : V → V → K) := V × K

class IsBilinear (B : V →  V → K) where
  llinear : ∀ r w v , B (r + w) v =  B r  v + B w  v
  rlinear : ∀ r w v , B w (r + v) = B w r + B  w v

namespace Heisenberg

variable [bilinearB : IsBilinear B]


instance : HMul (Heisenberg B) (Heisenberg B) (Heisenberg B) where
  hMul := fun a b => ⟨ a.1 + b.1 , a.2 + b.2 + B  a.1  b.1 ⟩

omit bilinearB in
lemma mul_def (a b : Heisenberg B) : a * b = ⟨ a.1 + b.1 , a.2+ b.2 + B a.1 b.1 ⟩ := rfl


instance instSemigroup : Semigroup (Heisenberg B) where
  mul := (· * · )
  mul_assoc := by
    intro a b c
    repeat rw [mul_def]
    ext
    · simp only [add_assoc]
    · simp_rw [IsBilinear.rlinear,IsBilinear.llinear]
      abel


instance instInv: Inv  ( Heisenberg B) where
   inv := fun a => ⟨ -a.1 , -a.2 + B  a.1  a.1⟩

omit bilinearB in
lemma inv_def (a : Heisenberg B) : a⁻¹ =  ⟨ -a.1 , -a.2 + B  a.1  a.1⟩ := rfl

@[simp]
lemma Blzero (b:  V) : B  0  b  = 0 := by
  have h : B 0 b = B 0 b := by rfl
  nth_rewrite 1 [←zero_add 0] at h
  rw [bilinearB.llinear] at h
  simp at h
  exact h

@[simp]
lemma Brzero (b:  V) : B  b 0 = 0 := by
  have h : B b 0 = B b 0 := by rfl
  nth_rewrite 1 [←zero_add 0] at h
  rw [bilinearB.rlinear] at h
  simp at h
  exact h

instance hasOne: One (Heisenberg B)  where
  one := ⟨0,0⟩

omit bilinearB in
@[simp]
lemma One_def1 : (1 :Heisenberg B).1 =0 := rfl

omit bilinearB in
@[simp]
lemma One_def2 : (1 :Heisenberg B).2 =0 := rfl


instance instMulOneClass : MulOneClass (Heisenberg B) where
  one_mul := by simp [mul_def]
  mul_one := by simp [mul_def]



instance instMonoid : Monoid (Heisenberg B) where
  one_mul := by simp
  mul_one := by simp
  npow := npowRecAuto
  npow_zero := by intros; rfl
  npow_succ := by intros; rfl

instance instGroup : Group (Heisenberg B) where
  one_mul := one_mul
  mul_one := mul_one
  inv_mul_cancel := by
    intro a
    rw [mul_def,inv_def]
    calc
      _ = ⟨0, B a.1 a.1 + B (-a.1) a.1⟩  := by simp
      _ = ⟨0, B 0 a.1⟩  := by simp [<-IsBilinear.llinear]
      _ = ⟨0,0⟩  := by simp [Blzero]
      _ = _ := by rfl



end Heisenberg

noncomputable section Eg

local notation "VV" => (ZMod 2)
local notation "KK" => (ZMod 2)

abbrev BB : VV → VV → KK := fun a b => a * b


abbrev a : Heisenberg (BB) := ⟨1,0⟩

example : a * a = ⟨0,1⟩ := by
  simp [Heisenberg.mul_def]
  ring_nf
  apply FiniteField.cast_card_eq_zero



end Eg


section QuadraticForm

open Heisenberg



variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V][Module K V]
variable (B : V → V → K )[bilinearB : IsBilinear B]



def form ( f: V → K) : ( V →  V →  K ) := fun x => (fun y => f (x+y) - f (x) - f (y))


class Quadraticform (f : V → K) where
bilinear : IsBilinear (form f)
sq_smul : ∀ (t : K) v , f ( t • v ) = t^2 * f (v)



class addQuadraticform (f : V → K)  where
Quadf : Quadraticform f
additive : ∀ a b , f (a+b) = f (a) + f (b)



variable (f : V → K )[Quadraticform f]

def nondegenerate (B : V → V → K) := ∀ v , (∀ w , B v w =0) → v = 0

#check nondegenerate B

def alternatingform (B : V → V → K) : (V → V → K )  := fun v => (fun w => B v w - B w v)

#check alternatingform B

abbrev C : Subgroup (Heisenberg B) := Subgroup.center _

instance SubK : Subgroup (Heisenberg B) where
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
omit [Module K V] in
theorem centralextension : (SubK B).carrier ⊆ (C B).carrier := by
  intro x h
  simp [SubK] at h
  rw [Subgroup.mem_carrier]
  rw [Subgroup.mem_center_iff]
  intro y
  repeat rw [mul_def]
  simp [add_comm , h]
--Subgroup.subgroupOf

omit [Module K V] in
theorem center_is_K_of_nondegenerateB (nondege: nondegenerate (alternatingform B) ) : (SubK B) = (C B) := by
  ext x
  constructor
  apply centralextension
  intro h
  simp [SubK , C] at h ⊢
  rw [Subgroup.mem_center_iff] at h
  simp_rw [mul_def] at h
  simp [add_comm] at h
  simp [nondegenerate , alternatingform] at nondege
  specialize nondege x.1
  exact nondege (by convert h using 1; simp [sub_eq_zero] ; tauto)
