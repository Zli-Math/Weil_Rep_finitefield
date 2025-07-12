import Mathlib
import WeilRepFinitefield.Compute
import WeilRepFinitefield.Heisenberg
import WeilRepFinitefield.QuadForm2

--import WeilRepFinitefield.Quadratic

section Symplectic_Group

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

variable (B : LinearMap.BilinForm K V) --[hnd : NonDegenerate (alternatingform B)]
--(nondegenerate_symplectic_form : nondegenerate (alternatingform B))

open Function

abbrev LinearMap.BilinForm.isAlt (B : LinearMap.BilinForm K V) (σ : V ≃ₗ[K] V) : Prop := ∀ w v, B (σ w) (σ v) - B w v = B (σ v) (σ w) - B v w

abbrev LinearMap.BilinForm.Sp := {σ : V ≃ₗ[K] V // B.isAlt σ }

namespace LinearMap.BilinForm.Sp



variable (σ : B.Sp)
variable {B}

lemma coe_map : σ.1 v  = σ v := rfl
lemma coe_map' : σ v  = σ.1 v := rfl


lemma preserveB : ∀ w v, B (σ w) (σ  v) - B w v = B (σ v) (σ w) - B v w := σ.2

lemma linear : ∀ w v, σ (w + v) = σ w + σ v := by
  simp only [coe_map', map_add, implies_true]

lemma slinear : ∀ (r : K) w, σ (r • w) = r • σ w := by
  intro r w
  simp only [coe_map', map_smul]

/-
lemma sym_auto_comp (σ₁ σ₂ : B.Sp) : ∀ w v, B ((σ₁ ∘ σ₂) w) ((σ₁ ∘ σ₂) v) - B w v = B ((σ₁ ∘ σ₂) v) ((σ₁ ∘ σ₂) w) - B v w := by
  intro w v
  simp [Function.comp,coe_map']
  have h₁ : B (σ₁ (σ₂ w)) (σ₁.1 (σ₂ v)) - B (σ₂ w) (σ₂ v) = B (σ₁ (σ₂ v)) (σ₁ (σ₂ w)) - B (σ₂ v) (σ₂ w) := σ₁.preserveB (σ₂ w) (σ₂ v)
  have h₂ : B (σ₂ w) (σ₂ v) - B w v = B (σ₂ v) (σ₂ w) - B v w := σ₂.2 w v
  linear_combination h₁ + h₂

-/

instance instFact_isALtclosed : Fact (∀ {a b}, B.isAlt a → B.isAlt b → B.isAlt (b.trans a)) where
  out :=  by
    intro σ₁ σ₂ p1 p2 w v
    have h₁ : B (σ₁ (σ₂ w)) (σ₁.1 (σ₂ v)) - B (σ₂ w) (σ₂ v) = B (σ₁ (σ₂ v)) (σ₁ (σ₂ w)) - B (σ₂ v) (σ₂ w) := p1 (σ₂ w) (σ₂ v)
    have h₂ : B (σ₂ w) (σ₂ v) - B w v = B (σ₂ v) (σ₂ w) - B v w := p2 w v
    simp only [LinearEquiv.trans_apply]
    linear_combination h₁ + h₂


--instance : HMul (B.Sp)  (B.Sp) (B.Sp) := SubGL.instHMul

--#synth HMul  B.Sp B.Sp B.Sp

variable (a b : B.Sp)

instance instFact_isAltOne : Fact (B.isAlt 1) where
  out := fun _ _ => by simp only [LinearEquiv.coe_one, id_eq, sub_self]


@[simp]
lemma map_one (v : V): (1 : Sp B) v = v := by rfl

#synth MulOneClass (Sp B)

instance instFact_isAutInv : Fact (∀ {σ}, B.isAlt σ → B.isAlt σ.symm) where
  out := by
    intro σ p w v
    have fun_inv_fun  : ∀ v, σ (σ.symm v)  = v
    := by simp only [LinearEquiv.apply_symm_apply, implies_true]
    have h :=  p (σ.symm w) (σ.symm v)
    repeat rw [fun_inv_fun] at h
    linear_combination -h

#synth Group B.Sp

end LinearMap.BilinForm.Sp
end Symplectic_Group

section PS_Group

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable (B : LinearMap.BilinForm K V) --[hnd : NonDegenerate (alternatingform B)]


abbrev LinearMap.BilinForm.associated (σ :V≃ₗ[K] V ) (f : QuadraticForm K V) := ∀ w v, QuadraticMap.polar f w v = B (σ w) (σ v) - B w v



abbrev LinearMap.BilinForm.Ps :=
  {σ : (V≃ₗ[K] V) × (QuadraticForm K V) // B.associated σ.1 σ.2}


section Compute
instance instDecidableassocidated [DecidableEq K] [Fintype V]: Decidable (B.associated σ f) := by
  infer_instance
/-
variable {n : ℕ}
variable [DecidableEq K]  [FinEnum K]

local notation "VV" => (Fin n → K)

variable (B : LinearMap.BilinForm K (VV))

#synth FinEnum $ (VV ≃ₗ[K]VV)
instance :FinEnum (QuadraticForm K VV) := QuadraticForm.instFinEnumQuadraticForm

#synth Decidable (B.associated )

instance instFinenum : FinEnum B.Ps := by
  unfold LinearMap.BilinForm.Ps
  apply FinEnum.Subtype.finEnum
-/

end Compute

namespace LinearMap.BilinForm.Ps

variable {B} in
abbrev σ (a : B.Ps):= a.1.1
variable {B} in
abbrev f (a : B.Ps):= a.1.2

@[simp]
lemma σ_def {a : V≃ₗ[K] V} {f : QuadraticForm K V} {h : B.associated a f} : σ (⟨(a,f),h⟩:B.Ps) = a  := rfl

@[simp]
lemma f_def {a : V≃ₗ[K] V} {ff : QuadraticForm K V} {h : B.associated a ff} : f (⟨(a,ff),h⟩:B.Ps) = ff  := rfl



lemma comp_associated  (a b : B.Ps) : ∀ w v, QuadraticMap.polar (b.f + ((a.f).comp (b.σ).toLinearMap)) w v = B ((a.σ * b.σ) w) ((a.σ * b.σ) v) - B w v := by
  sorry
  /-
  intro w v
  simp [form, Sp.mul_def]
  have h1 : b.f (w + v) - b.f w - b.f v = B (b.σ.σ w) (b.σ.σ v) - B w v := b.associatedB w v
  have h2 : a.f (b.σ.σ w +  b.σ.σ v) - a.f (b.σ.σ w) - a.f (b.σ.σ v) = B (a.σ.σ (b.σ.σ w)) (a.σ.σ (b.σ.σ v)) - B (b.σ.σ w) (b.σ.σ v) := by
    exact a.associatedB (b.σ.σ w) (b.σ.σ v)
  linear_combination h1 + h2
  -/

instance instHMul: HMul (B.Ps)  (B.Ps) (B.Ps) where
  hMul := fun a b =>  ⟨ ((a.σ) * (b.σ), b.f + ((a.f).comp  (b.σ).toLinearMap)), comp_associated B a b⟩



@[simp]
lemma  mul_def (a b : B.Ps) : a * b = ⟨ ((a.σ) * (b.σ), b.f + ((a.f).comp  (b.σ).toLinearMap)), comp_associated B a b⟩ := by rfl




instance instSemigroup : Semigroup (B.Ps) where
  mul := HMul.hMul
  mul_assoc := by
    intro a b c
    simp [mul_def]
    constructor
    · rfl
    · ext x
      simp only [f, σ, QuadraticMap.add_apply, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.coe_toLinearMap_mul, mul_apply]
      ring_nf


lemma inv_associated (σ : V ≃ₗ[K] V) (f : QuadraticForm K V) (hB : B.associated σ  f) : B.associated σ.symm ((-f).comp (σ.symm).toLinearMap) := by
  intro w v
  have h := @hB (σ.symm w) (σ.symm v)
  simp only [QuadraticMap.polar, QuadraticMap.comp_apply, LinearEquiv.coe_coe, map_add,
    QuadraticMap.neg_apply, sub_neg_eq_add]
  simp only [QuadraticMap.polar, LinearEquiv.apply_symm_apply] at h
  linear_combination - h

instance  instInv: Inv  (B.Ps) where
   inv := fun a => ⟨((a.σ).symm , (- a.f).comp  (a.σ).symm)  , inv_associated B a.σ a.f a.2⟩

lemma inv_def (a : B.Ps) : a⁻¹ = ⟨((a.σ).symm , (- a.f).comp  (a.σ).symm) , inv_associated B a.σ a.f a.2⟩ := by rfl

lemma one_associated : B.associated 1 0 := by
  simp [associated,QuadraticMap.polar]

instance hasOne: One (Ps B)  where
  one := ⟨(1 , 0), one_associated B⟩

@[simp]
lemma One_def : (1 : Ps B) = ⟨(1, 0), one_associated B⟩ := rfl

instance instMulOneClass : MulOneClass (B.Ps) where
  one_mul := by
    intro a
    rw [mul_def]
    simp only [One_def, σ_def, one_mul, f_def]
    simp only [One_def, one_mul,<-Subtype.val_inj]
    apply Prod.ext
    · ext x; rfl
    · ext x ; simp only [QuadraticMap.add_apply, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
      QuadraticMap.zero_apply, add_zero]
  mul_one := by
    intro a
    rw [mul_def]
    simp only [One_def, σ_def, mul_one, f_def, LinearEquiv.coe_toLinearMap_one, zero_add]
    simp only [One_def, one_mul,<-Subtype.val_inj]
    apply Prod.ext
    · ext x; rfl
    · ext x; simp only [LinearEquiv.coe_toLinearMap_one, zero_add, QuadraticMap.comp_apply, id_coe,
      id_eq]

instance instMonoid : Monoid (B.Ps) where
  one_mul := one_mul
  mul_one := mul_one


noncomputable instance instGroup : Group (Ps B) where
inv_mul_cancel := by
  intro a
  rw [mul_def,inv_def]
  simp
  constructor
  · ext; simp only [LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply, LinearEquiv.coe_one,
    id_eq]
  · ext; simp only [QuadraticMap.add_apply, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, QuadraticMap.neg_apply, add_neg_cancel, QuadraticMap.zero_apply]

end LinearMap.BilinForm.Ps

section Ps_action_on_Heisenberg

variable {B} in
abbrev LinearMap.BilinForm.Ps.smul (s : B.Ps) (h : B.Heisenberg): B.Heisenberg := (s.σ h.1, s.f h.1 + h.2)

instance LinearMap.BilinForm.instSmul : SMul (B.Ps) (B.Heisenberg) where
  smul := fun s h => s.smul h


@[simp]
lemma LinearMap.BilinForm.Ps.smul_def (s : B.Ps) (h : B.Heisenberg) : s • h =  (s.σ h.1, s.f h.1 + h.2) := by rfl

instance instMulAction : MulAction (B.Ps) (B.Heisenberg) where
  smul := SMul.smul
  one_smul := by
    intro b
    simp only [LinearMap.BilinForm.Ps.One_def, LinearMap.BilinForm.Ps.smul_def,
      LinearMap.BilinForm.Ps.σ_def, LinearEquiv.coe_one, id_eq, LinearMap.BilinForm.Ps.f_def,
      QuadraticMap.zero_apply, zero_add, Prod.mk.eta]
  mul_smul := by
    intro x y b
    simp only [LinearMap.BilinForm.Ps.mul_def, LinearMap.BilinForm.Ps.smul_def,
      LinearMap.BilinForm.Ps.σ_def, LinearEquiv.mul_apply, LinearMap.BilinForm.Ps.f_def,
      QuadraticMap.add_apply, QuadraticMap.comp_apply, LinearEquiv.coe_coe, Prod.mk.injEq, true_and,add_comm,add_assoc]




end Ps_action_on_Heisenberg
end PS_Group
