import Mathlib
--import WeilRepFinitefield.HeisenbergRepresentation
import WeilRepFinitefield.HeisenbergRepresentation
import WeilRepFinitefield.PseudoSymplecticGroup

open Module
open BigOperators
open Schrodinger_Model
open Finset Fintype
open Classical

variable {K : Type } [Field K]  {V : Type }  [AddCommGroup V] [Module K V] {R : Type*} [Field R]
variable (B : LinearMap.BilinForm K V)

local notation3 "⟪" a:40 "," b:40 "⟫" => (B.toAlt) a b

variable {X Y : Submodule K V} (χ₀ : AddChar K R) (P : B.Polarization X Y)
variable (h : B.Heisenberg)

variable (χ : (B.toSubgroup X) →* Rˣ) [isextendchara : extendcharacter B χ₀ χ]

variable (σ : B.Sp)
variable (s : B.Ps)
variable (v w : V)

@[simp]
lemma LinearMap.BilinForm.toAlt.llinear_form : ∀ w v r, ⟪w + r, v⟫ = ⟪w, v⟫ + ⟪r, v⟫ := by
  intro w v r
  simp only [LinearMap.sub_apply, map_add, LinearMap.add_apply, LinearMap.BilinForm.flip_apply]

@[simp]
lemma LinearMap.BilinForm.toAlt.rlinear_form : ∀ w v r, ⟪w, v + r⟫ = ⟪w, v⟫ + ⟪w, r⟫ := by
  intro w v r
  simp only [LinearMap.sub_apply, map_add, flip_apply, LinearMap.add_apply]


section


local notation "ρ" => (P.rhoY χ)

#check ρ

variable [Fintype K] [Fintype V] [DecidableEq K][DecidableEq V]

#synth HSMul (B.Ps) (B.Heisenberg) (B.Heisenberg)

variable {B} in
def LinearMap.BilinForm.Polarization.omega_aux (s : B.Ps) (w : V): End R (P.Ymodel R) :=
  ∑ (v : V) , ρ  ((s • (B.toH v))⁻¹ * (B.toH w) * (B.toH v))

#print LinearMap.BilinForm.Polarization.omega_aux

variable {B}

abbrev _root_.LinearMap.BilinForm.Ps.Ws := {v | ∀ w, s.σ w = w → (s.f w) =  ⟪v,w⟫}

lemma _root_.LinearMap.BilinForm.Ps.Ws_nonempty : Nonempty (s.Ws) := by sorry


variable [FiniteDimensional K V] [Nonempty V] [char2: CharP K 2]

/-
noncomputable section test

variable (α : Type*) [Fintype α]

#synth FinEnum α

end test
-/

variable [FinEnum V]

def _root_.LinearMap.BilinForm.Ps.ws : V :=
  let Ws := FinEnum.toList $ s.Ws
  match Ws with
  | [] => 0
  | h :: _ => h

abbrev LinearMap.BilinForm.Polarization.omega : End R (P.Ymodel R) := P.omega_aux χ s  (s.ws)

local notation "ω" => (P.omega χ)

open LinearMap.BilinForm
open Heisenberg
open Polarization

#check hmul_def

lemma weq_lemma (H : wₛ ∈ s.Ws):
∀ w : V, (s • h) * (s • B.toH w)⁻¹ * (B.toH wₛ) * (B.toH  w)  =  (s • B.toH (w - h.1))⁻¹ * (B.toH wₛ) * (B.toH (w - h.1)) * h := by
  intro w
  simp only [LinearMap.BilinForm.Ps.smul_def, LinearMap.BilinForm.toH_def, add_zero, map_sub,LinearMap.BilinForm.Heisenberg.mul_def]
  have h1: - s.σ (-h.1) = s.σ (h.1) := by simp only [map_neg, neg_neg]
  simp_rw [inv_def B]
  rw [Prod.ext_iff]
  constructor
  · simp [add_assoc]
    rw [← AddCommSemigroup.toAddSemigroup.add_assoc]
    simp only [sub_eq_add_neg]
  · sorry
    /-
    simp [add_assoc, add_comm]
    rw [← add_assoc, ← sub_eq_add_neg]
    have h2 :  s.f h.1 - s.f w = - s.f (w - h.1) -(B (s.σ (w - h.1)) (s.σ h.1) - B (w - h.1) h.1) := by
      rw [← s.associatedB]
      simp [form, ← sub_eq_add_neg]
      ring
    simp [h2, sub_eq_add_neg, add_assoc, Sp.linear]
    have : B (w + (-h.1 + (wₛ + (-s.σ (-h.1) + -s.σ w)))) h.1 = B (w + -h.1) h.1 + B (wₛ + (-s.σ (-h.1) + -s.σ w)) h.1 := by simp [← AddCommSemigroup.toAddSemigroup.add_assoc w, IsBilinear.llinear]
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
    -/


--Prop 3.2 (1)
omit isextendchara in
lemma omega_intertwine : (ρ (s • h)) ∘ₗ  (ω s) = (ω s) ∘ₗ (ρ h) := by
  unfold omega; unfold omega_aux
  rw [<-LinearMap.mul_eq_comp,Finset.mul_sum]
  rw [<-LinearMap.mul_eq_comp,Finset.sum_mul]
  simp_rw [rhoY.map_mul]
  set v := h.1
  sorry
  /-
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
  -/


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


--define gamma function
variable (s₁ s₂ : Ps B)(w₁ : s₁.Ws) (w₂ : s₂.Ws)(w₁₂ :(s₁ * s₂).Ws )

structure theta_function (θ : Sp B → ℝ) where
mod : θ 1 ≡ 0 [PMOD 2*π]

variable (θ : Sp B→ ℝ) (Hθ : theta_function θ)

structure gamma_function (γ : (Sp B) → ℂ) where
one : γ 1 = 1
eq : ∀ σ , γ σ = (1/2) ^ ((LinearMap.id - σ.1.1).rank.toNat / 2) * exp ^ (Complex.I * θ (σ))




abbrev I : AddSubgroup V where
  carrier := {u : V | ∃ w : V, w - s.σ w = u}
  add_mem' := by
    intro a b ha hb
    simp_all
    obtain ⟨w1, h1⟩ := ha
    obtain ⟨w2, h2⟩ := hb
    use (w1 + w2)
    rw [← h1, ← h2,Sp.linear, ← sub_sub]
    have : w1 + w2 - s.σ w1 - s.σ w2 = w1 - s.σ w1 + (w2 - s.σ w2) := by
      rw [sub_eq_add_neg _ (s.σ w1), add_assoc, add_comm w2 _, ← add_assoc, ← sub_eq_add_neg, add_sub]
    simp [this]
  zero_mem' := by
    simp
    have := Sp.slinear (s.σ) (0 : K) (w : V)
    simp at this
    use 0
    simp [this]
  neg_mem' := by
    intro x hx
    simp_all
    obtain ⟨w, hw⟩ := hx
    use (-w)
    have : -w = (-1 : K) • w := by rw [neg_one_smul]
    rw [this, Sp.slinear, ← smul_sub, hw, neg_one_smul]

abbrev I₀ := { (u₁, u₂) : (I s₁ w) × (I s₂ w)|  (u₁ : V) + u₂  = w₁₂ - w₁ - w₂}

instance FintypeI : Fintype (I₀ χ₀ w s₁ s₂ w₁ w₂ w₁₂) := Subtype.fintype _





--define cocycle Corollary 3.4
variable (γ : Sp B → ℂ) (Hγ : gamma_function θ γ)

def cocycle := γ (s₁.σ) * γ (s₂.σ) * (γ (s₁.σ * s₂.σ))⁻¹ * (∑ ((u₁, u₂) ∈ (I₀ χ₀ w s₁ s₂ w₁ w₂ w₁₂)), χ₀ (s₁.f u₁.2.choose + ⟪w₁.1, u₁.2.choose⟫ + B (u₁.2.choose - s₁.σ u₁.2.choose) (w₁.1 + u₁.2.choose) + s₂.f u₂.2.choose + ⟪w₂.1, u₂.2.choose⟫) * χ₀ (B (u₂.2.choose - s₂.σ u₂.2.choose) (w₂.1 + u₂.2.choose) + B ((u₁.2.choose - s₁.σ u₁.2.choose) + w₁.1) ((u₂.2.choose - s₂.σ u₂.2.choose) + w₂.1)))

local notation "c" => (cocycle χ₀ w s₁ s₂ w₁ w₂ w₁₂ γ )


abbrev Ker : AddSubgroup V where
  carrier := {w : V| s.σ w = w }
  add_mem' := by
    intro a b ha hb
    simp_all [Sp.linear]
  zero_mem' := by
    simp
    have := Sp.slinear (s.σ) (0 : K) (w : V)
    simp at this
    exact this
  neg_mem' := by
    intro x hx
    simp_all
    have : -x = (-1 : K) • x := by rw [neg_one_smul]
    rw [this, Sp.slinear]
    simp [hx]
instance FintypeK : Fintype (Ker s w) := Subtype.fintype _


def id_σ : AddMonoidHom V V where
  toFun := id - s.σ.1.toFun
  map_zero' := by simp
  map_add' := by
    intro x y
    simp
    rw [← sub_sub, sub_eq_add_neg (x + y) _, add_assoc, add_comm y _, ← add_assoc, add_sub, ← sub_eq_add_neg]

omit [Fintype K] [Fintype V] [FiniteDimensional K V] [Nonempty V] char2 hnd [IsBilinear B] in
lemma cong1 : Ker s w = (id_σ s).ker := by
  ext x
  constructor
  · simp [id_σ]
    intro h
    rw [Sp.coe_map, h]
    simp
  · simp [id_σ]
    intro h
    rw [Sp.coe_map] at h
    symm
    exact eq_of_sub_eq_zero h

omit [Fintype K] [Fintype V] [FiniteDimensional K V] [Nonempty V] char2 hnd [IsBilinear B] in
lemma cong2 : I s w = (id_σ s).range := by
  ext x
  constructor
  · simp [id_σ]
    intro v hv
    use v
    rw [Sp.coe_map, hv]
  · simp [id_σ]
    intro v hv
    use v
    rw [Sp.coe_map] at hv
    exact hv

def quotientkers : ∀ (s : Ps B), V ⧸ (Ker s w) ≃+ (I s w) := by
  intro s
  rw [cong1, cong2]
  exact QuotientAddGroup.quotientKerEquivRange (id_σ s)

--instance : HVAdd V (Ker s w) (V ⧸ Ker s w) := by sorry



local notation "Ks" => Fintype.card (Ker s w)



lemma weq' : ∀ w : V, (s • w : Heisenberg B)⁻¹ * (((ws χ₀ s), 0) : Heisenberg B) * ((w , 0) : Heisenberg B) = (w - s.σ w + ws χ₀ s, s.f w + ⟪ws χ₀ s, w⟫ + B (w - s.σ w) (ws χ₀ s + w))  := by
    intro w
    simp [Heisenberg.inv_def, Heisenberg.mul_def, pseudo_symplectic.smul_def]
    constructor
    · simp [add_comm, ←add_assoc, sub_eq_add_neg]
    · simp [alternatingform, IsBilinear.llinear]
      have h1 : B (s.σ w) (s.σ w) + B (- s.σ w) w =  B (w - s.σ w) w:= by
        simp [sub_eq_add_neg, IsBilinear.llinear]
        have eq1 : s.f w + s.f w = 0:= by
          simp [← two_mul]
          left
          apply CharP.ofNat_eq_zero
        have eq2 : B (s.σ w) (s.σ w) - B w w = s.f (w + w) := by
          rw [← s.associatedB w w]
          simp [form, sub_sub, eq1]
        suffices h : s.f (w + w) = 0
        rw [h] at eq2
        rw [← add_left_inj (B w w)] at eq2
        simp at eq2
        exact eq2
        have : w + w = 0 := by rw [← two_smul K w, CharTwo.two_eq_zero, zero_smul]
        rw [this]
        have : s.f ((0 : K) • 0) = 0 ^ 2 * s.f 0 := by apply s.Quaf.sq_smul 0 0
        simp at this
        exact this
      have h2 : - s.f w = s.f w := CharTwo.neg_eq (s.f w)
      simp [add_assoc, h2]
      rw [← add_assoc, ← add_assoc, add_comm, sub_add]
      simp [sub_eq_add_neg]
      rw [add_comm (B (s.σ w) (s.σ w)) _, add_assoc, h1]
      simp [IsBilinear.llinear, IsBilinear.rlinear]
      ring_nf
      simp [add_assoc, sub_eq_add_neg, IsBilinear.llinear]

lemma weq'' : let f := fun x:V => (rhoY hp χ) ((s • x : Heisenberg B)⁻¹ * (((ws χ₀ s), 0) : Heisenberg B) * (x , 0)); ∀ v ∈ Ker s w, f (w + v) = f w:= by
  intro f v hv

  have : ∀ x, f x =  (χ₀ (s.f x + ⟪(ws χ₀ s),x⟫ + B (x - s.σ x) ((ws χ₀ s) + x))) • ρ (x - s.σ x + (ws χ₀ s)) := by
    intro x
    simp [f, weq']
    apply rhoY.eq'
  simp [this]

  have : s.f (w + v) = s.f w + s.f v + B (s.σ w) (s.σ v) - B w v := by
    rw [← add_sub, ← Ps.associatedB s w v, form]
    ring
  simp [this]
  simp [Ker] at hv

  have : w + v - s.σ (w + v) = w - s.σ w := by
    simp [Sp.linear, sub_eq_add_neg, add_assoc]
    simp [← add_assoc]
    rw [← sub_eq_add_neg, sub_eq_zero]
    symm
    exact hv
  simp [this]
  rw [← add_assoc (ws χ₀ s: V) w v ]
  simp [IsBilinear.rlinear ((ws χ₀ s) + w) (w - s.σ w) v]

  have : B (s.σ w) (s.σ v) - B w v + B (w - s.σ w) v = 0 := by
    simp [sub_eq_add_neg, IsBilinear.llinear, hv]
    ring_nf
    simp [← IsBilinear.llinear]
  rw [add_comm (B (w - s.σ w) (↑(ws χ₀ s) + w)) _, add_assoc, ← add_assoc (⟪↑(ws χ₀ s),w + v⟫) _ _, add_comm (⟪↑(ws χ₀ s),w + v⟫) _, ← add_assoc, ← add_assoc, ← add_sub, add_assoc (s.f w + s.f v) _ _]
  simp [this, rlinear_form]

  have : χ₀ (s.f w + s.f v + (⟪↑(ws χ₀ s),w⟫ + ⟪↑(ws χ₀ s),v⟫) + B (w - s.σ w) (↑(ws χ₀ s) + w)) = χ₀ (s.f v +  ⟪↑(ws χ₀ s),v⟫) * χ₀ (s.f w + ⟪↑(ws χ₀ s),w⟫ + B (w - s.σ w) (↑(ws χ₀ s) + w)) := by
    calc
      _ = χ₀ (s.f v +  ⟪↑(ws χ₀ s),v⟫ + s.f w + ⟪↑(ws χ₀ s),w⟫ + B (w - s.σ w) (↑(ws χ₀ s) + w)) := by
        rw [add_comm (s.f w), add_assoc (s.f v), ← add_assoc (s.f w), add_comm _ (⟪↑(ws χ₀ s),v⟫), ← add_assoc, ← add_assoc]
      _ = χ₀ (s.f v + ⟪↑(ws χ₀ s),v⟫) * χ₀ (s.f w + ⟪↑(ws χ₀ s),w⟫ + B (w - s.σ w) (↑(ws χ₀ s) + w)) := by
        rw [add_assoc, add_assoc, ← add_assoc (s.f w)]
        apply AddChar.map_add_eq_mul χ₀ (s.f v + ⟪↑(ws χ₀ s),v⟫) (s.f w + ⟪↑(ws χ₀ s),w⟫ + B (w - s.σ w) (↑(ws χ₀ s) + w))
  simp [this]
  rw [← smul_smul, ← rhoY.eq']

  have : χ₀ (s.f v + ⟪↑(ws χ₀ s),v⟫) = 1 := by
    rw [AddChar.map_add_eq_mul χ₀ (s.f v) _]
    have := (ws χ₀ s).2
    simp only [Ws] at this
    rw [Set.mem_setOf] at this
    have H := this v hv
    rw [← H, ← AddChar.map_add_eq_mul]
    have : s.f v + s.f v = 0:= by
      simp [← two_mul]
      left
      apply CharP.ofNat_eq_zero
    rw [this]
    exact AddChar.map_zero_eq_one χ₀

  simp [this]

lemma coset_eq : let f := fun x:V => (rhoY hp χ) ((s • x : Heisenberg B)⁻¹ * (((ws χ₀ s), 0) : Heisenberg B) * (x , 0)); (Ks : ℂ)⁻¹ • ( ∑ v : V, f (v)) =  (∑ u : I s w, f u.2.choose) := by
  intro f
  have : ∑ v : V, f v = (Ks : ℂ) • (∑ x : V ⧸ Ker s w, f x.out ):= by
    --have : V = ⋃(x : V ⧸ Ker s w), Quotient.out x +ᵥ (Ker s w) := by sorry
    sorry
  rw [this]
  let g := fun u : I s w => f u.2.choose
  have hequiv : Function.Bijective (quotientkers w s).1 := by apply Equiv.bijective (quotientkers w s).1
  have hg : ∑ x : V ⧸ (Ker s w), f x.out = ∑  x : V ⧸ (Ker s w), g ((quotientkers w s).1 x) := by
    simp
    sorry
  rw [hg, smul_smul, inv_mul_cancel_of_invertible, one_smul]
  apply Function.Bijective.sum_comp hequiv g


--Prop 3.2 (2)
lemma omega_eq : ∀ s, (Fintype.card (Ker s w) : ℂ)⁻¹ • ω s =  (∑ (u : (I s w)), χ₀ ((s.f u.2.choose) + ⟪ws χ₀ s, u.2.choose⟫ + B u (ws χ₀ s + u.2.choose )) • ρ (u + ws χ₀ s)) := by
  unfold omega; unfold omega_aux
  intro s
  rw [coset_eq]
  simp only [weq']
  set f := fun u : I s w => (rhoY hp χ) (u.2.choose - s.σ u.2.choose + (ws χ₀ s), s.f u.2.choose + ⟪(ws χ₀ s), u.2.choose⟫ + B (u.2.choose - s.σ u.2.choose) ((ws χ₀ s) + u.2.choose))
  have : ∀ u, f u =  (χ₀ (s.f u.2.choose + ⟪(ws χ₀ s), u.2.choose⟫ + B (u) (ws χ₀ s + u.2.choose) )) • ρ (u + (ws χ₀ s)) := by
    intro x
    simp [f]
    have : ∀ u : (I s w), u.2.choose - s.σ u.2.choose = u := by
      intro u
      have := u.2
      apply Exists.choose_spec this
    rw [this]
    apply rhoY.eq'
  simp [this]



--Proof of Corollory 3.4
lemma cocycle_omega : (γ (s₁.σ) • ((Fintype.card (Ker s₁ w) : ℂ)⁻¹ • ω s₁)) * (γ (s₂.σ) • (((Fintype.card (Ker s₂ w) : ℂ)⁻¹) • ω s₂)) =  c • (γ (s₁.σ * s₂.σ) • ((Fintype.card (Ker (s₁ * s₂) w) : ℂ)⁻¹) •  ω (s₁ * s₂)):= by
  simp only [omega_eq]
  rw [mul_smul_comm, smul_mul_assoc, Finset.sum_mul_sum]
  have : ∀ (i : I s₁ w) (j : I s₂ w), χ₀ (s₁.f (i.2.choose) + ⟪(ws χ₀ s₁), i.2.choose⟫ + B i ((ws χ₀ s₁) + i.2.choose)) • (rhoY hp χ) (i + (ws χ₀ s₁)) * χ₀ (s₂.f j.2.choose + ⟪(ws χ₀ s₂), j.2.choose⟫ + B j ((ws χ₀ s₂) + j.2.choose)) • (rhoY hp χ) (j + (ws χ₀ s₂)) =  (χ₀ (s₁.f i.2.choose + ⟪(ws χ₀ s₁), i.2.choose⟫ + B (i.2.choose - s₁.σ i.2.choose) ((ws χ₀ s₁) + i.2.choose) + s₂.f j.2.choose + ⟪ws χ₀ s₂, j.2.choose⟫) * χ₀ (B (j.2.choose - s₂.σ j.2.choose) (ws χ₀ s₂ + j.2.choose) + B ((i.2.choose - s₁.σ i.2.choose) + (ws χ₀ s₁)) ((j.2.choose - s₂.σ j.2.choose) + ws χ₀ s₂)))• (rhoY hp χ) (i + j + (ws χ₀ s₁) + (ws χ₀ s₂)) := by
    intro x y
    rw [smul_mul_smul_comm]
    have h1 : (rhoY hp χ) ( x + (ws χ₀ s₁)) * (rhoY hp χ) (y + (ws χ₀ s₂)) = χ₀ (B (x + (ws χ₀ s₁)) (y + (ws χ₀ s₂))) • (rhoY hp χ) ( x + y + (ws χ₀ s₁) + (ws χ₀ s₂)) := by
      rw [rhoY.map_mul]
      simp [Heisenberg.mul_def]
      rw [rhoY.eq' B χ₀ hp χ]
      congr 2
      simp [add_assoc]
      simp [← add_assoc]
      rw [add_comm]
    rw [h1, smul_smul]
    simp [← AddChar.map_add_eq_mul]
    congr 2
    simp [add_assoc]
    have := Exists.choose_spec x.2
    simp [this]
    have := Exists.choose_spec y.2
    simp [this]
  simp_rw [this]






  sorry


--Corollory 3.6
lemma range_of_cocycle : c ∈ ({1, -1} : Set ℂ ) ↔ ∀ w1 w2, B (s₁.σ w1) (s₁.σ w2) = B w1 w2 ∧ B (s₂.σ w1) (s₂.σ w2) = B w1 w2 ∧ θ s₁.σ + θ s₂.σ - θ (s₁.σ * s₂.σ) ≡ 0 [PMOD π] := by
  constructor
  · intro h w1 w2
    sorry
  · sorry





class value_of_cocycle where
value : c  ∈ ({1, -1} : Set ℂ )

variable [Gamma_condition: value_of_cocycle χ₀ w s₁ s₂ w₁ w₂ w₁₂ γ]


--Define Weil representation of Ps B
--Definition 3.8
structure cover_of_Ps where
s : Ps B
integer : ℤ
omega : End ℂ (Ymodel hp)
relation :  omega = (-1 : ℂ) ^ integer • ω s


--Corollory 3.10
structure Weil_rep where
rep : cover_of_Ps χ₀ hp χ →  End ℂ (Ymodel hp)
equation : ∀ (s : cover_of_Ps χ₀ hp χ), rep s = s.3


structure Character_of_Weil_rep (s : cover_of_Ps χ₀ hp χ) where
existw : ∃ w, s.s.σ w - w = ws χ₀ s.s
char := fun (s : cover_of_Ps χ₀ hp χ) => (-1 : ℂ) ^ (s.integer) * γ (s.s.σ) * Fintype.card (Y) * χ₀ (s.s.f existw.choose - B (s.s.σ existw.choose) (ws χ₀ s.s))



end
