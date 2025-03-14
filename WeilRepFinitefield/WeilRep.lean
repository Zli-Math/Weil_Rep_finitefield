import Mathlib
import WeilRepFinitefield.HeisenbergRepresentation
import WeilRepFinitefield.PseudoSymplecticGroup

open Module
open BigOperators
open Heisenberg pseudo_symplectic Sp Schrodinger_model
open Finset Fintype

variable {K : Type } [Field K] [Fintype K] {V : Type } [Fintype V] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

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
  ∑ (v : V) , ρ ((σ v : Heisenberg B)⁻¹ * (w) * v)



abbrev Ws := {v | ∀ w, s.σ w = 0 → χ₀ (s.f w) = χ₀  ⟪v,w⟫}

lemma Ws.nonempty : Nonempty (Ws χ₀ s) := by sorry

def ws := Nonempty.some $ Ws.nonempty χ₀ s

abbrev omega : End ℂ (Ymodel hp) := omega_aux hp χ s.σ  (ws χ₀ s)

local notation "ω" => (omega χ₀ hp χ)

lemma weq_lemma (H : wₛ ∈ Ws χ₀ s):
∀ w, h * (s.σ w: Heisenberg B)⁻¹ * (wₛ) * w =  (s.σ (w-h.1): Heisenberg B)⁻¹ * (wₛ)  * (w-h.1) * h := by sorry


lemma omega_intertwine : (ρ h) ∘ₗ  (ω s) = (ω s) ∘ₗ (ρ h) := by
  unfold omega; unfold omega_aux
  rw [<-LinearMap.mul_eq_comp,Finset.mul_sum]
  rw [<-LinearMap.mul_eq_comp,Finset.sum_mul]
  simp_rw [rhoY.map_mul]
  set v := h.1
  have weq : ∀ w, h * (s.σ w: Heisenberg B)⁻¹ * (ws χ₀ s) * w =  (s.σ (w-v): Heisenberg B)⁻¹ * (ws χ₀ s)  * (w-v) * h :=
    weq_lemma χ₀ h s (ws χ₀ s).2
  set f := fun (w:V) => (rhoY hp χ) ((s.σ w : Heisenberg B)⁻¹ * (ws χ₀ s) * w * h)
  set e := fun (w:V) => w-v
  calc
  _ =  ∑ w : V, (rhoY hp χ) ((s.σ (w-v) : Heisenberg B)⁻¹ * (ws χ₀ s) * (w-v) * h) := by
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





end
