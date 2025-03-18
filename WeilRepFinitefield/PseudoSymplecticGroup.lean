import Mathlib
import WeilRepFinitefield.Quadratic

section Pseudo_Symplectic_Group

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

variable (B : V → V → K ) --[hnd : NonDegenerate (alternatingform B)]
--(nondegenerate_symplectic_form : nondegenerate (alternatingform B))

open Function

--symplectic_form
local notation "B_s" => (alternatingform B)

--symplectic_space
structure symplectic_space where
space := V
form := B_s

variable (V_s: symplectic_space B)


@[ext]
structure Sp where
σ : V ≃ₗ[K] V
preserveB : ∀ w v, B (σ w) (σ v) - B w v = B (σ v) (σ w) - B v w

namespace Sp



instance Sp_funlike : FunLike (Sp B) V V where
  coe := fun s => s.σ
  coe_injective' := by intro a b h; ext; simp [h]



variable (σ : Sp B)
lemma coe_map : σ.σ v  = σ v := rfl


lemma preserveB' : ∀ w v, B (σ w) (σ  v) - B w v = B (σ v) (σ w) - B v w := σ.preserveB

variable {B} in
lemma linear : ∀ w v, σ (w + v) = σ w + σ v := by
  intro w v; rw [DFunLike.coe,Sp_funlike]
  simp only [map_add]

variable {B} in
lemma slinear : ∀ (r : K) w, σ (r • w) = r • σ w := by
  intro r w
  rw [DFunLike.coe,Sp_funlike]
  simp only [map_smul]


lemma sym_auto_comp (σ₁ σ₂ : Sp B) : ∀ w v, B ((σ₁ ∘ σ₂) w) ((σ₁ ∘ σ₂) v) - B w v = B ((σ₁ ∘ σ₂) v) ((σ₁ ∘ σ₂) w) - B v w := by
  intro w v
  simp [Function.comp]
  have h₁ : B (σ₁ (σ₂ w)) (σ₁.1 (σ₂ v)) - B (σ₂ w) (σ₂ v) = B (σ₁ (σ₂ v)) (σ₁ (σ₂ w)) - B (σ₂ v) (σ₂ w) := σ₁.preserveB (σ₂ w) (σ₂ v)
  have h₂ : B (σ₂ w) (σ₂ v) - B w v = B (σ₂ v) (σ₂ w) - B v w := σ₂.preserveB w v
  linear_combination h₁ + h₂

instance : HMul (Sp B)  (Sp B) (Sp B) where
  hMul := fun a b =>  ⟨b.σ.trans a.σ, sym_auto_comp B _ _ ⟩

variable (a b : Sp B)
--omit hnd in
lemma  mul_def : a * b = ⟨b.1.trans a.1, sym_auto_comp B _ _⟩:= rfl


@[simp]
lemma map_mul (a b : Sp B) (v : V): (a * b) v = a ( b v ) := by
  rw [mul_def]
  calc
  _ = (b.σ.trans a.σ ) v := by rfl


instance instSemigroup : Semigroup (Sp B) where
  mul := HMul.hMul
  mul_assoc := by
    intro a b c
    simp [mul_def]
    rfl

instance hasOne: One (Sp B)  where
  one := ⟨1, by simp⟩

lemma One_def : (1 : Sp B) = ⟨1,by simp⟩  := rfl

@[simp]
lemma map_one (v : V): (1 : Sp B) v = v := by rfl

instance instMulOneClass : MulOneClass (Sp B) where
  one_mul := by
    intro a
    simp [mul_def]
    aesop
  mul_one := by
    intro a
    simp [mul_def]
    aesop


instance instMonoid : Monoid (Sp B) where
  one_mul := one_mul
  mul_one := mul_one
  npow := npowRecAuto
  npow_zero := by intros; rfl
  npow_succ := by intros; rfl

variable {B} in
lemma inv_aux : ∀ w v, B (σ.1.symm w) (σ.1.symm v) - B w v = B (σ.1.symm v) (σ.1.symm w) - B v w := by
    intro w v
    have fun_inv_fun  : ∀ v, σ.σ (σ.1.symm v)  = v
    := by simp
    have h : B (σ.1 (σ.1.symm w)) (σ.1 (σ.1.symm v)) - B (σ.1.symm w) (σ.1.symm v) = B (σ.1 (σ.1.symm v)) (σ.1 (σ.1.symm w)) - B (σ.1.symm v) (σ.1.symm w):= by simp only [σ.preserveB]
    repeat rw [fun_inv_fun] at h
    linear_combination -h


instance instGroup : Group (Sp B) where
  inv := fun σ=> ⟨σ.1.symm, inv_aux σ⟩
  inv_mul_cancel := by
    intro a
    ext v
    calc
    _ = a.σ.symm (a.σ v) := by simp [mul_def]
    _ = _ := by rw [One_def];simp only [LinearEquiv.symm_apply_apply,
      LinearEquiv.coe_one, id_eq]

lemma inv_def: σ⁻¹ = ⟨σ.1.symm, inv_aux σ⟩ := rfl

@[simp]
lemma self_of_map_inv_self : σ⁻¹ (σ v) = v := by
  simp only [← map_mul, inv_mul_cancel, map_one]

@[simp]
lemma self_of_map_self_inv : σ (σ⁻¹ v) = v := by
  simp only [← map_mul, mul_inv_cancel, map_one]

end Sp

namespace pseudo_symplectic

open Heisenberg Function Sp

variable (f : V → K)

@[ext]
structure Ps where
σ : Sp B
f : V → K
Quaf : Quadraticform f
associatedB : ∀ w v, form f w v = B (σ w) (σ v) - B w v

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
    · intro r w v
      simp [form]
      have hf : f (r • w + v) - f (r • w) - f v = r * (f (w + v) - f w - f v) := by
        have hf' := h1.bilinear.lslinear r w v
        simp_all [form]
      have hg : g (r • w + v) - g (r • w) - g v = r * (g (w + v) - g w - g v) := by
        have hg' := h2.bilinear.lslinear r w v
        simp_all [form]
      calc
        _ = (f (r • w + v) - f (r • w) - f v) + (g (r • w + v) - g (r • w) - g v) := by ring
        _ = r * (f (w + v) - f w - f v) + r * (g (w + v) - g w - g v) := by simp [hf, hg]
        _ = r * (f (w + v) + g (w + v) - (f w + g w) - (f v + g v)) := by ring
    · intro r w v
      simp [form]
      have hf : f (w + r • v) - f w - f (r • v) = r * (f (w + v) - f w - f v) := by
        have hf' := h1.bilinear.rslinear r w v
        simp_all [form]
      have hg : g (w + r • v) - g w - g (r • v) = r * (g (w + v) - g w - g v) := by
        have hg' := h2.bilinear.rslinear r w v
        simp_all [form]
      calc
        _ = (f (w + r • v) - f w - f (r • v)) + (g (w + r • v) - g w - g (r • v)) := by ring
        _ = r * (f (w + v) - f w - f v) + r * (g (w + v) - g w - g v) := by simp [hf, hg]
        _ = r * (f (w + v) + g (w + v) - (f w + g w) - (f v + g v)) := by ring
  · intro t v
    calc
      _ = f (t • v) + g (t • v) := by rfl
      _ = t^2 * f v + t^2 * g v := by rw [h1.2, h2.2]
      _ = t^2 * (f (v) + g (v)) := by ring


lemma comp_quadraricform (f : V → K) (σ : Sp B) (h : Quadraticform f) : Quadraticform (f ∘ σ) := by
  constructor
  · constructor
    · intro r w v
      simp [form]
      have h' : f (σ.σ (r + w + v)) - f (σ.σ (r + w)) - f (σ.σ v) = f (σ.σ r + σ.σ w + σ.σ v) - f (σ.σ r + σ.σ w) - f (σ.σ v) := by simp only [map_add]
      repeat rw [Sp.coe_map] at h'
      rw [h']
      have h'' := h.bilinear.llinear (σ.σ r) (σ.σ w) (σ.σ v)
      repeat rw [Sp.coe_map] at h''
      simp_all [form]
      rw [linear σ r v, linear σ w v]
    · intro r w v
      simp [form]
      have h' : f (σ.σ (w + (r + v))) - f (σ.σ (w)) - f (σ.σ (r + v)) = f (σ.σ w + (σ.σ r + σ.σ v)) - f (σ.σ w) - f (σ.σ r + σ.σ v):= by simp [add_assoc, linear σ]
      repeat rw [Sp.coe_map] at h'
      rw [h']
      have h'' := h.bilinear.rlinear (σ.σ r) (σ.σ w) (σ.σ v)
      repeat rw [Sp.coe_map] at h''
      simp_all [← add_assoc, form]
      rw [linear σ w r, linear σ w v]
    · intro r w v
      simp [form, Sp.linear, Sp.slinear]
      exact h.bilinear.lslinear r (σ w) (σ v)
    · intro r w v
      simp [form, Sp.linear, Sp.slinear]
      exact h.bilinear.rslinear r (σ w) (σ v)
  · intro t v
    calc
      _ = f (t • (σ  v)) := by simp [slinear]
      _ = t^2 * f (σ.1 v):= by rw [coe_map,h.2]
      _ = t^2 * ((f ∘ σ.1) (v)) := by simp


lemma comp_associatedB  (a b : Ps B) : ∀ w v, form (b.2 + a.2 ∘ b.1.1) w v = B ((a.σ * b.σ).1 w) ((a.1 * b.1).1 v) - B w v := by
  intro w v
  simp [form, Sp.mul_def]
  have h1 : b.f (w + v) - b.f w - b.f v = B (b.σ.σ w) (b.σ.σ v) - B w v := b.associatedB w v
  have h2 : a.f (b.σ.σ w +  b.σ.σ v) - a.f (b.σ.σ w) - a.f (b.σ.σ v) = B (a.σ.σ (b.σ.σ w)) (a.σ.σ (b.σ.σ v)) - B (b.σ.σ w) (b.σ.σ v) := by
    exact a.associatedB (b.σ.σ w) (b.σ.σ v)
  linear_combination h1 + h2

instance : HMul (Ps B)  (Ps B) (Ps B) where
  hMul := fun a b =>  ⟨a.σ * b.σ, b.f + a.f ∘ b.1, add_quadraticform (b.f) (a.f ∘ b.σ) (b.3) (comp_quadraricform B a.f b.σ a.3), comp_associatedB B a b⟩


lemma  mul_def (a b : Ps B) : a * b = ⟨a.1 * b.1, b.f + a.f ∘ b.1, add_quadraticform (b.2) (a.2 ∘ b.1.1) (b.3) (comp_quadraricform B a.2 b.1 a.3), comp_associatedB B a b⟩:= rfl

instance instSemigroup : Semigroup (Ps B) where
  mul := HMul.hMul
  mul_assoc := by
    intro a b c
    simp [mul_def]
    constructor
    · rfl
    · ext x
      simp [add_assoc]

variable {B} in
lemma neg_comp_quadratic (σ : Sp B) {f : V → K} (h : Quadraticform f) : Quadraticform ((-f) ∘ (σ)) := by
  constructor
  · constructor
    · intro r w v
      simp [form]
      have h := h.bilinear.llinear (σ r) (σ w) (σ v)
      simp [form,<-Sp.linear] at h
      linear_combination -h
    · intro r w v
      simp [form]
      have h := h.bilinear.rlinear (σ r) (σ w) (σ v)
      simp [form,<-Sp.linear] at h
      linear_combination -h
    · intro r w v
      simp [form, Sp.linear, Sp.slinear]
      have h := h.bilinear.lslinear r (σ w) (σ v)
      simp_all [form]
      linear_combination -h
    · intro r w v
      simp [form, Sp.linear, Sp.slinear]
      have h := h.bilinear.rslinear r (σ w) (σ v)
      simp_all [form]
      linear_combination -h
  · intro t v
    simp [h.sq_smul,Sp.slinear]



variable {B} in
lemma inv_associatedB (σ : Sp B) {f : V → K} (hB : ∀ w v, form f  w v = B (σ w) (σ v) - B w v ): ∀ w v, form ((-f) ∘ (σ⁻¹:Sp B)) w v = B (σ⁻¹ w) (σ⁻¹ v) - B w v := by
  intro w v
  simp [form,linear]
  have h := hB (σ⁻¹ w) (σ⁻¹ v)
  rw [form] at h
  simp only [<-Sp.map_mul,mul_inv_cancel, Sp.map_one] at h
  linear_combination - h

instance  instInv: Inv  (Ps B) where
   inv := fun a => ⟨a.σ⁻¹ , (- a.f) ∘ (a.σ⁻¹ : Sp B) , neg_comp_quadratic (a.σ⁻¹) a.Quaf, inv_associatedB a.σ a.associatedB⟩

--omit hnd in
lemma inv_def (a : Ps B) : a⁻¹ =
⟨a.σ⁻¹ , (- a.f) ∘ (a.σ⁻¹ : Sp B) , neg_comp_quadratic (a.σ⁻¹) a.Quaf, inv_associatedB a.σ a.associatedB⟩ := rfl


lemma one_quadraticform : Quadraticform (0 : V → K) := by
  constructor
  · constructor
    · intro r w v
      simp [form]
    · intro r w v
      simp [form]
    · intro r w v
      simp [form]
    · intro r w v
      simp [form]
  · intro t v
    simp

--omit hnd in
lemma one_associatedB : ∀ w v, form 0 w v = B ((1 : Sp B) w) ((1 : Sp B) v) - B w v := by
  intro w v
  simp [form]

instance hasOne: One (Ps B)  where
  one := ⟨(1 : Sp B), 0, one_quadraticform, one_associatedB B⟩



@[simp]
lemma One_def : (1 : Ps B) = ⟨(1 : Sp B), 0, one_quadraticform, one_associatedB B⟩ := rfl



instance instMulOneClass : MulOneClass (Ps B) where
  one_mul := by
    intro a
    rw [mul_def]
    ext v;unfold Ps.σ
    · rw [One_def,coe_map,Sp.map_mul,Sp.map_one,Sp.coe_map]
    · simp only [One_def, Pi.zero_comp, Pi.add_apply, Pi.zero_apply, add_zero]
  mul_one := by
    intro a
    rw [mul_def]
    ext v
    · rw [One_def,coe_map,Sp.map_mul,Sp.map_one,Sp.coe_map]
    · simp only [One_def, Pi.add_apply, Pi.zero_apply, comp_apply, zero_add]
      rfl




instance instMonoid : Monoid (Ps B) where
  one_mul := one_mul
  mul_one := mul_one
  npow := npowRecAuto
  npow_zero := by intros; rfl
  npow_succ := by intros; rfl

noncomputable instance instGroup : Group (Ps B) where
inv_mul_cancel := by
  intro a
  rw [mul_def,inv_def]
  ext v
  · simp only [inv_mul_cancel, One_def]
  · simp only [Pi.add_apply, comp_apply, coe_map, self_of_map_inv_self, Pi.neg_apply,
    add_neg_cancel, One_def, Pi.zero_apply]

instance instSmul : SMul (Ps B) (Heisenberg B) where
  smul := fun s h => (s.σ h.1, s.f h.1 + h.2)

lemma smul_def (s : Ps B) (h : Heisenberg B) : s • h =  (s.σ h.1, s.f h.1 + h.2) := by rfl

instance instMulAction : MulAction (Ps B) (Heisenberg B) where
  smul := SMul.smul
  one_smul := by
    intro b
    simp [smul_def]
  mul_smul := by
    intro x y b
    simp [smul_def, mul_def, ← add_assoc, add_comm]




end pseudo_symplectic

end Pseudo_Symplectic_Group
