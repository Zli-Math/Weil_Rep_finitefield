import Mathlib
import WeilRepFinitefield.HeisenbergRepresentation
import WeilRepFinitefield.PseudoSymplecticGroup

open Module
open BigOperators
open Heisenberg pseudo_symplectic Sp Schrodinger_model
open Finset Fintype
open Classical

variable {K : Type } [Field K] [Fintype K] {V : Type } [Fintype V] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nonempty V]

variable {B : V → V → K} [IsBilinear B]
variable [hnd : NonDegenerate (alternatingform B)]

local notation3 "⟪" a:40 "," b:40 "⟫" => (alternatingform B) a b

variable {X Y : Submodule K V} (χ₀ : AddChar K ℂˣ) (hp : polarization B X Y)
variable (h : Heisenberg B)

variable (χ : (subXK B (X := X)) →* ℂˣ) [isextendchara : extendcharacter B χ₀ χ]

variable (σ : Sp B)
variable (s : Ps B)
variable (v w : V)

#check ⟪v,w⟫

noncomputable section

local notation "ρ" => (rhoY hp χ)


abbrev omega_aux : End ℂ (Ymodel hp) :=
  ∑ (v : V) , ρ ((s • v : Heisenberg B)⁻¹ * (w) * v)



abbrev Ws := {v | ∀ w, s.σ w = 0 → χ₀ (s.f w) = χ₀  ⟪v,w⟫}

lemma Ws.nonempty : Nonempty (Ws χ₀ s) := by sorry

def ws := Nonempty.some $ Ws.nonempty χ₀ s

abbrev omega : End ℂ (Ymodel hp) := omega_aux hp χ s  (ws χ₀ s)

local notation "ω" => (omega χ₀ hp χ)

omit [Fintype K] [Fintype V] [FiniteDimensional K V] hnd in
lemma weq_lemma (H : wₛ ∈ Ws χ₀ s):
∀ w : V, (s • h) * (s • w: Heisenberg B)⁻¹ * wₛ * w  =  (s • (w - h.1): Heisenberg B)⁻¹ * wₛ * (w - h.1) * h := by
  intro w
  simp [Heisenberg.inv_def, Heisenberg.mul_def, pseudo_symplectic.smul_def]
  have h1: - s.σ (-h.1) = s.σ (h.1) := by rw [← neg_one_smul K h.1, Sp.slinear, neg_one_smul K (s.σ h.1), neg_neg]
  constructor
  · simp [add_assoc]
    rw [← add_assoc]
    simp [sub_eq_add_neg, Sp.linear]
    simp [h1]
  · simp [add_assoc, add_comm]
    rw [← add_assoc, ← sub_eq_add_neg]
    have h2 :  s.f h.1 - s.f w = - s.f (w - h.1) -(B (s.σ (w - h.1)) (s.σ h.1) - B (w - h.1) h.1) := by
      rw [← s.associatedB]
      simp [form, ← sub_eq_add_neg]
      ring
    simp [h2, sub_eq_add_neg, add_assoc, Sp.linear]
    have : B (w + (-h.1 + (wₛ + (-s.σ (-h.1) + -s.σ w)))) h.1 = B (w + -h.1) h.1 + B (wₛ + (-s.σ (-h.1) + -s.σ w)) h.1 := by simp [← add_assoc w, IsBilinear.llinear]
    simp [this]
    rw [add_comm (B (w + -h.1) h.1) (B (wₛ + (-s.σ (-h.1) + -s.σ w)) h.1)]
    have h3 : B (wₛ + (-s.σ (-h.1) + -s.σ w)) (w + -h.1) + (B (wₛ + (-s.σ (-h.1) + -s.σ w)) h.1 + B (w + -h.1) h.1) = B (w + -h.1) h.1 + B (wₛ + (-s.σ (-h.1) + -s.σ w)) w := by
      simp [add_comm, add_assoc, IsBilinear.rlinear]
      rw [add_comm, add_assoc, ← IsBilinear.rlinear, neg_add_cancel, Brzero B (wₛ + (-s.σ w + -s.σ (-h.1)))]
      simp
    rw [h3, h1]
    simp [← add_assoc, add_comm]
    simp [add_assoc, IsBilinear.llinear, IsBilinear.rlinear]
    rw [← neg_one_smul K h.1, Sp.slinear]
    simp only [IsBilinear.lslinear, IsBilinear.rslinear]
    ring_nf
    have : B (s.σ h.1) (-s.σ w) = - B (s.σ h.1) (s.σ w) := by
      rw [← neg_one_mul, ← IsBilinear.rslinear (-1) (s.σ h.1) (s.σ w), neg_one_smul]
    simp [this]
    rw [add_sub, ← sub_eq_add_neg, ← sub_eq_add_neg]

omit isextendchara in
lemma omega_intertwine : (ρ (s • h)) ∘ₗ  (ω s) = (ω s) ∘ₗ (ρ h) := by
  unfold omega; unfold omega_aux
  rw [<-LinearMap.mul_eq_comp,Finset.mul_sum]
  rw [<-LinearMap.mul_eq_comp,Finset.sum_mul]
  simp_rw [rhoY.map_mul]
  set v := h.1
  have weq : ∀ w : V, (s • h) * (s • w: Heisenberg B)⁻¹ * (ws χ₀ s) * w =  (s • (w - v): Heisenberg B)⁻¹ * (ws χ₀ s)  * (w - v) * h := weq_lemma χ₀ h s (ws χ₀ s).2
  set f := fun (w:V) => (rhoY hp χ) ((s • w : Heisenberg B)⁻¹ * (ws χ₀ s) * w * h)
  set e := fun (w:V) => w - v
  calc
  _ =  ∑ w : V, (rhoY hp χ) ((s • (w-v) : Heisenberg B)⁻¹ * (ws χ₀ s) * (w-v) * h) := by
    apply Fintype.sum_congr
    intro w; congr 1;
    rw [<-weq w]
    group
  _= ∑ w : V, f (e w):= by
    apply Fintype.sum_congr
    intro; simp only [Set.mem_setOf_eq, Prod.mk_sub_mk, sub_self, _root_.map_mul, f, e]
  _ = ∑ w : V, f (w) := by
    refine Function.Bijective.sum_comp ?_ f
    constructor
    · apply Function.LeftInverse.injective (g:= fun w => w+v)
      intro x; simp [e]
    · apply Function.RightInverse.surjective (g:= fun w => w+v)
      intro x; simp [e]
  _ = _ := by
    apply Fintype.sum_congr
    intro; simp only [Set.mem_setOf_eq, Prod.mk_sub_mk, sub_self, _root_.map_mul, f, e]


/-
  _ = ∑ w , f ((fun w => w-v) w) := by
    apply Fintype.sum_congr
    intro ; simp [f]
  -- - = ∑ w, f w := by sorry
  _ = _ := by
    --apply Function.Bijective.sum_comp ?_ f
    sorry
-/
/-
  _ =  ∑ w : V, (rhoY hp χ) ((s.σ (w-v) : Heisenberg B)⁻¹ * (ws χ₀ s) * (w-v) * h) := by
    apply Fintype.sum_congr
    intro w; congr 1;
    rw [<-weq w]
    group
  _ = _ := by
    let f := fun (w:V) => (rhoY hp χ) ((s.σ w : Heisenberg B)⁻¹ * (ws χ₀ s) * w * h)
    --apply Function.Bijective.sum_comp ?_ f
    sorry
-/

variable (s₁ s₂ : Ps B)(w₁ : Ws χ₀ s₁) (w₂ : Ws χ₀ s₂)(w₁₂ : Ws χ₀ (s₁ * s₂))

structure theta_function (θ : Sp B → ℝ) where
mod : θ 1 ≡ 0 [PMOD 2*π]

variable (θ : Sp B→ ℝ) (Hθ : theta_function θ)

structure gamma_function (γ : (Sp B) → ℂ) where
one : γ 1 = 1
eq : ∀ σ , γ σ = (1/2) ^ ((LinearMap.id - σ.1.1).rank.toNat / 2) * exp ^ (Complex.I * θ (σ))

abbrev I := {u : V | ∃ w : V, w - s.σ w = u}

abbrev I₀ := { (u₁, u₂) : (I s₁) × (I s₂)|  (u₁ : V) + u₂  = w₁₂ - w₁ - w₂}

instance FintypeI : Fintype (I₀ χ₀ s₁ s₂ w₁ w₂ w₁₂) := Subtype.fintype _

variable (γ : Sp B → ℂ) (Hγ : gamma_function θ γ)

--cocycle
def c := γ (s₁.σ) * γ (s₂.σ) * (γ (s₁.σ * s₂.σ))⁻¹ * (∑ ((u₁, u₂) ∈ (I₀ χ₀ s₁ s₂ w₁ w₂ w₁₂)), χ₀ (s₁.f u₁.2.choose + ⟪w₁.1, u₁.2.choose⟫ + B (u₁.2.choose - s₁.σ u₁.2.choose) (w₁.1 + u₁.2.choose) + s₂.f u₂.2.choose + ⟪w₂.1, u₂.2.choose⟫) * χ₀ (B (u₂.2.choose - s₂.σ u₂.2.choose) (w₂.1 + u₂.2.choose) + B ((u₁.2.choose - s₁.σ u₁.2.choose) + w₁.1) ((u₂.2.choose - s₂.σ u₂.2.choose) + w₂.1)))

def Ker := {w : V| s.σ w = w }
instance FintypeK : Fintype (Ker s) := Subtype.fintype _

local notation "Ks" => Fintype.card (Ker s)

lemma omega_eq : ω s = (Ks : ℂ ) • (∑ (u : (I s)), χ₀ ((s.f w) + ⟪ws χ₀ s, w⟫ + B u (w + ws χ₀ s)) • ρ (u + ws χ₀ s)) := by sorry


lemma cocycle_omega : (γ (s₁.σ) • (ω s₁)) * (γ (s₂.σ) • (ω s₂)) = (c χ₀ s₁ s₂ w₁ w₂ w₁₂ γ) • (γ (s₁.σ * s₂.σ) • ω (s₁ * s₂)):= by sorry

lemma range_of_cocycle : c χ₀ s₁ s₂ w₁ w₂ w₁₂ γ ∈ ({1, -1} : Set ℂ ) ↔ ∀ w1 w2, B (s₁.σ w1) (s₁.σ w2) = B w1 w2 ∧ B (s₂.σ w1) (s₂.σ w2) = B w1 w2 ∧ θ s₁.σ + θ s₂.σ - θ (s₁.σ * s₂.σ) ≡ 0 [PMOD π] := by sorry

structure cover_of_Ps where
s : Ps B
omega : End ℂ (Ymodel hp)
relation : ∀ s k,  omega = (-1 : ℂ) ^ k • ω s

structure Weil_rep where
rep : cover_of_Ps χ₀ hp χ →  End ℂ (Ymodel hp)
equation : ∀ (s : cover_of_Ps χ₀ hp χ), rep s = s.2




end
