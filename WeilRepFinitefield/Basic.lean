import Mathlib

section HeisenbergGroup

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
variable (B : V → V → K)


abbrev Heisenberg (_ : V → V → K) := V × K

class IsBilinear (B : V →  V → K) where
  llinear : ∀ r w v , B (r + w) v =  B r v + B w v
  rlinear : ∀ r w v , B w (r + v) = B w r + B w v

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

end HeisenbergGroup



section Eg

local notation "VV" => (ZMod 2)
local notation "KK" => (ZMod 2)

abbrev BB : VV → VV → KK := fun a b => a * b

abbrev a : Heisenberg (BB) := ⟨1,0⟩

example : a * a = ⟨0,1⟩ := by
  simp [Heisenberg.mul_def]
  ring_nf
  apply FiniteField.cast_card_eq_zero

end Eg



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

end Quadratic_Form



section Pseudo_Symplectic_Group

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

variable (B : V → V → K ) (nondegenerate_symplectic_form : nondegenerate (alternatingform B))

open Function

--symplectic_form
local notation "B_s" => (alternatingform B)

--symplectic_space
structure symplectic_space where
space := V
form := B_s

variable (V_s: symplectic_space B)


--Symplectic group Sp(V)
namespace symplectic

@[ext]
structure symplectic_automorphism where
σ : V → V
bijective : Bijective σ
preserveB : ∀ w v, B (σ w) (σ v) - B w v = B (σ v) (σ w) - B v w
linear : ∀ w v, σ (w +  v) = σ w + σ v
slinear : ∀ (r : K) w, σ (r • w) = r • σ w

lemma sym_auto_comp (σ₁ σ₂ : symplectic_automorphism B) : ∀ w v, B ((σ₁.1 ∘ σ₂.1) w) ((σ₁.1 ∘ σ₂.1) v) - B w v = B ((σ₁.1 ∘ σ₂.1) v) ((σ₁.1 ∘ σ₂.1) w) - B v w := by
  intro w v
  simp [Function.comp]
  have h₁ : B (σ₁.1 (σ₂.1 w)) (σ₁.1 (σ₂.1 v)) - B (σ₂.1 w) (σ₂.1 v) = B (σ₁.1 (σ₂.1 v)) (σ₁.1 (σ₂.1 w)) - B (σ₂.1 v) (σ₂.1 w) := σ₁.preserveB (σ₂.1 w) (σ₂.1 v)
  have h₂ : B (σ₂.1 w) (σ₂.1 v) - B w v = B (σ₂.1 v) (σ₂.1 w) - B v w := σ₂.preserveB w v
  linear_combination h₁ + h₂


lemma comp_linear (σ₁ σ₂ : symplectic_automorphism B) : ∀ w v, (σ₁.1 ∘ σ₂.1) (w + v) = (σ₁.1 ∘ σ₂.1) w + (σ₁.1 ∘ σ₂.1) v := by
  intro w v
  simp [Function.comp, σ₂.4, σ₁.4]

lemma comp_slinear (σ₁ σ₂ : symplectic_automorphism B) : ∀ (r : K) v, (σ₁.1 ∘ σ₂.1) (r • v) = r • ((σ₁.1 ∘ σ₂.1) v) := by
  intro r v
  simp [Function.comp, σ₂.5, σ₁.5]


instance : HMul (symplectic_automorphism B)  (symplectic_automorphism B) (symplectic_automorphism B) where
  hMul := fun σ₁ σ₂ =>  ⟨σ₁.1 ∘  σ₂.1, Bijective.comp σ₁.2 σ₂.2, sym_auto_comp B σ₁ σ₂, comp_linear B σ₁ σ₂, comp_slinear B σ₁ σ₂⟩


lemma  mul_def (a b : symplectic_automorphism B) : a * b = ⟨a.1 ∘ b.1, Bijective.comp a.2 b.2 ,sym_auto_comp B a b, comp_linear B a b, comp_slinear B a b⟩:= rfl


instance instSemigroup : Semigroup (symplectic_automorphism B) where
  mul := HMul.hMul
  mul_assoc := by
    intro a b c
    simp [mul_def]
    rfl


lemma sym_auto_inv (σ : symplectic_automorphism B) : ∀ w v, B (invFun σ.1  w) (invFun σ.1 v) - B w v = B (invFun σ.1 v) (invFun σ.1 w) - B v w := by
   intro w v
   have h : B (σ.1 (invFun σ.1 w)) (σ.1 (invFun σ.1 v)) - B (invFun σ.1  w) (invFun σ.1 v) = B (σ.1 (invFun σ.1 v)) (σ.1 (invFun σ.1 w)) - B (invFun σ.1 v) (invFun σ.1 w):= by rw [σ.preserveB]
   rw [invFun_eq (σ.bijective.2 w), invFun_eq (σ.bijective.2 v)] at h
   linear_combination -h

lemma inv_bijective (σ : V → V) (h : Bijective σ ) : Bijective (invFun σ) := by
  apply bijective_iff_has_inverse.2
  use σ
  constructor
  · exact RightInverse.leftInverse (rightInverse_invFun h.2)
  · exact LeftInverse.rightInverse (leftInverse_invFun h.1)

lemma inv_linear (σ : symplectic_automorphism B) : ∀ w v, invFun σ.1 (w + v) = invFun σ.1 w + invFun σ.1 v := by
  intro w v
  have h : σ.1 (invFun σ.1 ( w + v)) = σ.1 ((invFun σ.1 w) +  (invFun σ.1 v) ):= by
    rw [σ.linear]
    rw [invFun_eq (σ.bijective.2 (w + v)), invFun_eq (σ.bijective.2 w), invFun_eq (σ.bijective.2 v)]
  apply σ.bijective.1 at h
  exact h

lemma inv_slinear (σ : symplectic_automorphism B) : ∀ (r : K) v,  invFun σ.1 (r • v) = r • ((invFun σ.1) v) := by
  intro r v
  have h : σ.1 (invFun σ.1 ( r • v)) = σ.1 (r • (invFun σ.1 v) ):= by
    rw [σ.slinear]
    rw [invFun_eq (σ.bijective.2 (r • v)), invFun_eq (σ.bijective.2 v)]
  apply σ.bijective.1 at h
  exact h

noncomputable instance  instInv: Inv  ( symplectic_automorphism B) where
   inv := fun a => ⟨invFun a.1, inv_bijective a.1 a.2, sym_auto_inv B a, inv_linear B a, inv_slinear B a⟩

lemma inv_def (a : symplectic_automorphism B) : a⁻¹ =  ⟨invFun a.1, inv_bijective a.1 a.2, sym_auto_inv B a,  inv_linear B a, inv_slinear B a⟩ := by rfl

instance hasOne: One (symplectic_automorphism B)  where
  one := ⟨id, Function.bijective_id, by simp, by simp, by simp⟩

@[simp]
lemma One_def : (1 : symplectic_automorphism B) = ⟨id, Function.bijective_id, by simp, by simp, by simp⟩  := rfl



instance instMulOneClass : MulOneClass (symplectic_automorphism B) where
  one_mul := by
    intro a
    simp [mul_def]

  mul_one := by
    intro a
    simp [mul_def]


instance instMonoid : Monoid (symplectic_automorphism B) where
  one_mul := one_mul
  mul_one := mul_one
  npow := npowRecAuto
  npow_zero := by intros; rfl
  npow_succ := by intros; rfl

noncomputable instance instGroup : Group (symplectic_automorphism B) where
  inv_mul_cancel := by
    intro a
    simp [inv_def, mul_def]
    apply Function.invFun_comp a.2.1

end symplectic



--pseudo_symplectic_group
namespace pseudo_symplectic

open Heisenberg Function symplectic

variable (f : V → K)

@[ext]
structure pseudo_symgrp where
σ : symplectic_automorphism B
f : V → K
Quaf : Quadraticform f
associatedB : ∀ w v, form f w v = B (σ.1 w) (σ.1 v) - B w v

lemma add_quadraticform (f : V → K ) (g : V → K) (h1 : Quadraticform f) (h2 : Quadraticform g) : Quadraticform (f + g) := by
  constructor
  · constructor
    · intro r w v
      simp [form]
      have hf : f (r + w + v) - f (r + w) - f v = f (r + v) - f r - f v + f (w + v) - f w - f v := by
        have hf' := h1.bilinear.llinear r w v
        simp_all [form]
        ring
      have hg : g (r + w + v) - g (r + w) - g v = g (r + v) - g r - g v + g (w + v) - g w - g v := by
        have hg' := h2.bilinear.llinear r w v
        simp_all [form]
        ring
      calc
        _ = (f (r + w + v) - f (r + w) - f v) + (g (r + w + v) - g (r + w) - g v) := by ring
        _ = (f (r + v) - f r - f v + f (w + v) - f w - f v) + (g (r + v) - g r - g v + g (w + v) - g w - g v) := by simp [hf, hg]
        _ = f (r + v) + g (r + v) - (f r + g r) - (f v + g v) + (f (w + v) + g (w + v) - (f w + g w) - (f v + g v)) := by ring
    · intro r w v
      simp [form]
      have hf : f (w + (r + v)) - f (w) - f (r + v) = f (w + r) - f w - f r + f (w + v) - f w - f v := by
        have hf' := h1.bilinear.rlinear r w v
        simp_all [form]
        ring
      have hg : g (w + (r + v)) - g (w) - g (r + v) = g (w + r) - g w - g r + g (w + v) - g w - g v := by
        have hg' := h2.bilinear.rlinear r w v
        simp_all [form]
        ring
      calc
        _ = (f (w + (r + v)) - f (w) - f (r + v)) + (g (w + (r + v)) - g (w) - g (r + v)) := by ring
        _ = (f (w + r) - f w - f r + f (w + v) - f w - f v) + (g (w + r) - g w - g r + g (w + v) - g w - g v) := by simp [hf, hg]
        _ = f (w + r) + g (w + r) - (f w + g w) - (f r + g r) + (f (w + v) + g (w + v) - (f w + g w) - (f v + g v)) := by ring
  · intro t v
    calc
      _ = f (t • v) + g (t • v) := by rfl
      _ = t^2 * f v + t^2 * g v := by rw [h1.2, h2.2]
      _ = t^2 * (f (v) + g (v)) := by ring

lemma comp_quadraricform (f : V → K) (σ : symplectic_automorphism B) (h : Quadraticform f) : Quadraticform (f ∘ (σ.1)) := by
  constructor
  · constructor
    · intro r w v
      simp [form]
      have h' : f (σ.σ (r + w + v)) - f (σ.σ (r + w)) - f (σ.σ v) = f (σ.σ r + σ.σ w + σ.σ v) - f (σ.σ r + σ.σ w) - f (σ.σ v) := by simp [σ.4]
      rw [h']
      have h'' := h.bilinear.llinear (σ.σ r) (σ.σ w) (σ.σ v)
      simp_all [form]
      rw [σ.4 r v, σ.4 w v]
    · intro r w v
      simp [form]
      have h' : f (σ.σ (w + (r + v))) - f (σ.σ (w)) - f (σ.σ (r + v)) = f (σ.σ w + (σ.σ r + σ.σ v)) - f (σ.σ w) - f (σ.σ r + σ.σ v):= by simp [add_assoc, σ.4]
      rw [h']
      have h'' := h.bilinear.rlinear (σ.σ r) (σ.σ w) (σ.σ v)
      simp_all [← add_assoc, form]
      rw [σ.4 w r, σ.4 w v]
  · intro t v
    calc
      _ = f (t • (σ.1  v)) := by simp [σ.5]
      _ = t^2 * f (σ.1 v):= by rw [h.2]
      _ = t^2 * ((f ∘ σ.1) (v)) := by simp

lemma comp_associatedB  (a b : pseudo_symgrp B) : ∀ w v, form (b.2 + a.2 ∘ b.1.1) w v = B ((a.1 * b.1).1 w) ((a.1 * b.1).1 v) - B w v := by
  intro w v
  simp [form, symplectic.mul_def]
  have h1 : b.f (w + v) - b.f w - b.f v = B (b.σ.σ w) (b.σ.σ v) - B w v := b.associatedB w v
  have h2 : a.f (b.σ.σ (w + v)) - a.f (b.σ.σ w) - a.f (b.σ.σ v) = B (a.σ.σ (b.σ.σ w)) (a.σ.σ (b.σ.σ v)) - B (b.σ.σ w) (b.σ.σ v) := by
    rw [b.σ.4]
    exact a.associatedB (b.σ.σ w) (b.σ.σ v)
  linear_combination h1 + h2

instance : HMul (pseudo_symgrp B)  (pseudo_symgrp B) (pseudo_symgrp B) where
  hMul := fun a b =>  ⟨a.1 * b.1, b.2 + a.2 ∘ b.1.1, add_quadraticform (b.2) (a.2 ∘ b.1.1) (b.3) (comp_quadraricform B a.2 b.1 a.3), comp_associatedB B a b⟩

lemma  mul_def (a b : pseudo_symgrp B) : a * b = ⟨a.1 * b.1, b.2 + a.2 ∘ b.1.1, add_quadraticform (b.2) (a.2 ∘ b.1.1) (b.3) (comp_quadraricform B a.2 b.1 a.3), comp_associatedB B a b⟩:= rfl

instance instSemigroup : Semigroup (pseudo_symgrp B) where
  mul := HMul.hMul
  mul_assoc := by
    intro a b c
    simp [mul_def]
    constructor
    · rfl
    · simp [symplectic.mul_def]
      ext x
      simp [add_assoc]

lemma inv_quadratic (a : pseudo_symgrp B) : Quadraticform ((- a.2) ∘ (invFun (a.1.1))) := by
  constructor
  · constructor
    · intro r w v
      simp [form, inv_linear]
      have h := a.3.bilinear.llinear (invFun a.σ.σ r) (invFun a.σ.σ w) (invFun a.σ.σ v)
      simp [form] at h
      linear_combination -h
    · intro r w v
      simp [form, inv_linear]
      have h := a.3.bilinear.rlinear (invFun a.σ.σ r) (invFun a.σ.σ w) (invFun a.σ.σ v)
      simp [form] at h
      linear_combination -h
  · intro t v
    simp [inv_slinear, a.3.sq_smul]

lemma inv_associatedB (a : pseudo_symgrp B) : ∀ w v, form ( (- a.2) ∘ (invFun (a.1.1))) w v = B (invFun a.1.1 w) (invFun a.1.1 v) - B w v := by
  intro w v
  simp [form, inv_linear]
  have h := a.associatedB (invFun a.σ.σ w) (invFun a.σ.σ v)
  simp [form] at h
  rw [invFun_eq (a.1.bijective.2 w), invFun_eq (a.1.bijective.2 v)] at h
  linear_combination -h

noncomputable instance  instInv: Inv  (pseudo_symgrp B) where
   inv := fun a => ⟨a.1⁻¹ , (- a.2) ∘ (invFun (a.1.1)) , inv_quadratic B a, inv_associatedB B a⟩

lemma inv_def (a : pseudo_symgrp B) : a⁻¹ =  ⟨a.1⁻¹ , (- a.2) ∘ (invFun (a.1.1)) , inv_quadratic B a, inv_associatedB B a⟩:= by rfl

lemma one_quadraticform : Quadraticform (0 : V → K) := by
  constructor
  · constructor
    · intro r w v
      simp [form]
    · intro r w v
      simp [form]
  · intro t v
    simp

lemma one_associatedB : ∀ w v, form 0 w v = B ((1 : symplectic_automorphism B).1 w) ((1 : symplectic_automorphism B).1 v) - B w v := by
  intro w v
  simp [form]

instance hasOne: One (pseudo_symgrp B)  where
  one := ⟨(1 : symplectic_automorphism B), 0, one_quadraticform, one_associatedB B⟩

@[simp]
lemma One_def : (1 : pseudo_symgrp B) = ⟨(1 : symplectic_automorphism B), 0, one_quadraticform, one_associatedB B⟩ := rfl



instance instMulOneClass : MulOneClass (pseudo_symgrp B) where
  one_mul := by
    intro a
    simp [mul_def]
    constructor
  mul_one := by
    intro a
    simp [mul_def]
    constructor


instance instMonoid : Monoid (pseudo_symgrp B) where
  one_mul := one_mul
  mul_one := mul_one
  npow := npowRecAuto
  npow_zero := by intros; rfl
  npow_succ := by intros; rfl

noncomputable instance instGroup : Group (pseudo_symgrp B) where
inv_mul_cancel := by
  intro a
  simp [mul_def, inv_def, comp_assoc]
  rw [invFun_comp]
  simp
  exact a.1.bijective.1

end pseudo_symplectic

end Pseudo_Symplectic_Group



section Schrodinger_Model_of_Heisenberg_Representation

open Heisenberg symplectic pseudo_symplectic Function


variable {K : Type*} [Field K] [Fintype K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

variable (X Y : Submodule K V)(n := Module.finrank K X)

abbrev HX := X × K














end Schrodinger_Model_of_Heisenberg_Representation
