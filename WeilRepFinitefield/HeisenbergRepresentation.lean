import Mathlib
import WeilRepFinitefield.Quadratic
import WeilRepFinitefield.Schrodinger_Model


noncomputable section Heisenberg_Representation
open Schrodinger_Model Heisenberg Function

set_option maxHeartbeats 400000

variable {K : Type } [hfK : Field K] [Fintype K] {V : Type } [hcV : AddCommGroup V] [hmV : Module K V] [FiniteDimensional K V] (B : V → V → K) [IsBilinear B] {X Y : Submodule K V} (χ₀ : AddChar K ℂˣ) (hp : polarization B X Y) (χ : (subXK B (X := X)) →* ℂˣ) [isextendchara : extendcharacter B χ₀ χ] (x : X) [char2: CharP K 2]



abbrev rho_aux (h : Heisenberg B) : Module.End ℂ (Schrodinger_model B χ)
  where
  toFun := fun f => ⟨fun h2 => f.1 (h⁻¹ * h2), Sch_act_mem B χ f.2 h⁻¹⟩
  map_add' := by
    intro f1 f2
    apply ext; intro h'
    simp_all only
    obtain ⟨val_1, property_1⟩ := f1
    obtain ⟨val_2, property_2⟩ := f2
    obtain ⟨fst_1, snd_1⟩ := h'
    simp_all only
    rfl
  map_smul' := by
    intro m x_1
    simp_all only [RingHom.id_apply]
    obtain ⟨val_1, property_1⟩ := x_1
    simp_all only
    rfl



def rho : Heisenberg B  →* Module.End ℂ (Schrodinger_model B χ) where
  toFun := rho_aux B χ
  map_one' := by unfold rho_aux; simp ; rfl
  map_mul' := by
    intro a b
    ext f y
    unfold rho_aux
    simp [Heisenberg.mul_def, Heisenberg.inv_def]
    have eq : -B a.1 b.1 + (-b.2 + -a.2) + B (a.1 + b.1) (a.1 + b.1) + y.2 + B (-b.1 + -a.1) y.1 = -b.2 + B b.1 b.1 + (-a.2 + B a.1 a.1 + y.2 + B (-a.1) y.1) + B (-b.1) (-a.1 + y.1):= by
      have : - B a.1 b.1 + B (a.1 + b.1) (a.1 + b.1) + B (-b.1 + -a.1) y.1 =  B b.1 b.1 + B a.1 a.1 + B (-a.1) y.1 + B (-b.1) (-a.1 + y.1) := by
        simp_all [IsBilinear.llinear, IsBilinear.rlinear]
        rw [← add_assoc (-B a.1 b.1), add_comm (B a.1 a.1), ← add_assoc (-B a.1 b.1), neg_add_cancel, zero_add, add_comm (B b.1 b.1), add_comm (B b.1 a.1), ← add_assoc (B a.1 a.1)]
        simp [add_assoc]
        rw [add_comm (B (-b.1) y.1), ← add_assoc, add_comm (B b.1 a.1)]
        simp [add_assoc]
        rw [← neg_one_smul K b.1, ← neg_one_smul K a.1]
        simp only [IsBilinear.lslinear, IsBilinear.rslinear]
        simp
      rw [add_comm (-B a.1 b.1), add_assoc _ y.2 _, add_comm y.2, ← add_assoc, add_assoc (-b.2 + -a.2), add_assoc (-b.2 + -a.2), this]
      rw [add_assoc (-b.2), ← add_assoc (-a.2), ← add_assoc (-a.2), ← add_assoc (-a.2), add_comm (-a.2), add_assoc (B b.1 b.1), ← add_assoc (-b.2),  ← add_assoc (-b.2), ← add_assoc (-b.2)]
      simp [add_assoc]
      rw [add_comm _ y.2, ← add_assoc, add_comm _ y.2, add_assoc]
    rw [eq, add_assoc]

-- The GeneralLinearGroup packet in mathlib is not good, so choose not to define it as linearEquiv
--def rho : Heisenberg B  →* LinearMap.GeneralLinearGroup ℂ (Schrodinger_model B χ):= MonoidHom.toHomUnits (rho_aux1 B χ)

variable {B} in
abbrev Ymodel (hp: polarization B X Y):= Y → ℂ

variable {B} in
def homY (hp : polarization B X Y) : (Schrodinger_model B χ) ≃ₗ[ℂ] (Ymodel hp) where
  toFun := fun f => (fun y => f.1 y)
  map_add' := by intro a b; simp; rfl
  map_smul' := by intro m n; simp; rfl
  invFun := fun g => (⟨fun (w : Heisenberg B) => χ (⟨((X_coor B hp w).1, w.2 - B (Y_coor B hp w).1 (X_coor B hp w).1 ), by simp [subXK, Set.prod]⟩)⁻¹ * g ⟨(Y_coor B hp w).1, by simp⟩, by
    simp [Schrodinger_model]
    intro a b w t w₀
    have hw : w ∈ X := by simp [subXK, Set.prod] at w₀; exact w₀
    simp [XY_coor_linear, Heisenberg.mul_def]
    rw [← mul_assoc, ← mul_inv_rev]
    norm_cast
    rw [← MonoidHom.map_mul χ]
    simp [Heisenberg.mul_def]
    norm_cast
    have hB : B a w - B (Y_coor B hp (a, b) + Y_coor B hp (w, t)) ((X_coor B hp (a,b)).1 + w)  = B (X_coor B hp (a,b)).1 w - B (X_coor B hp (a,b)).1 (Y_coor B hp (a, b)).1 := by
      have hab : a = (X_coor B hp (a,b)).1 + (Y_coor B hp (a,b)).1 := by
        have := element_XY B hp (a,b)
        simp [Set.prod] at this
        exact this
      nth_rw 1 [hab]
      simp [IsBilinear.llinear, IsBilinear.rlinear]
      rw [Y_coor_of_X B hp w t hw]
      simp [Brzero, X_coor, Y_coor]
      have:= hp.5
      simp [alternatingform] at this
      rw [← sub_eq_zero]
      apply this _ _ _ _
      simp
      simp
    simp only [← add_sub (b + t), Y_coor_add_X B hp a _ w hw]
    simp only [Y_coor]
    have hw' := X_in_X B hp w t hw
    have hw'' := Y_coor_of_X B hp w t hw
    congr 2
    congr 2
    congr 2
    · rw [← Heisenberg.mul_def B ((a,b) : Heisenberg B) (w,t)]
      simp [XY_coor_linear, hw']
    · rw [← Heisenberg.mul_def B ((a,b) : Heisenberg B) (w,t)]
      simp [hw''] at hB
      simp [Y_coor] at hB
      simp [XY_coor_linear, hw']
      rw [hB, sub_eq_add_neg, sub_eq_add_neg, add_comm (B _ w), add_assoc _ t _, ← add_assoc t, add_comm t]
      simp [← add_assoc]
      have:= hp.4
      simp [alternatingform] at this
      rw [← sub_eq_zero]
      apply this _ _ _ _
      simp
      simp⟩)
  left_inv := by
    simp [LeftInverse]
    intro f hf
    ext w
    symm
    nth_rw 1 [element_XY' B hp w]
    simp [Schrodinger_model] at hf
    have := hf (Y_coor B hp w) 0 (X_coor B hp w) (w.2 - B (Y_coor B hp w) (X_coor B hp w))
    apply this
  right_inv := by
    simp [Function.RightInverse, LeftInverse]
    intro g
    ext y
    have : Y_coor B hp (y,0) = y := by
      have hY := Y_in_Y B hp y 0 (by simp)
      norm_cast at hY
    rw [this, X_coor_of_Y B hp]
    have : B y (0 : X) = 0 := by
      norm_cast
      rw [Brzero B y]
    rw [← neg_eq_zero] at this
    simp only [this]
    have := χ.map_one'
    have one : (1 : subXK B X) = ⟨((0 : X), (0 : K)), by simp [subXK, Set.prod]⟩ := by rfl
    have h2 := χ.toFun_eq_coe
    rw [one, h2] at this
    rw [this]
    norm_cast
    rw [inv_one]
    norm_cast
    rw [one_mul]
    simp

variable {B} in
def rhoY : Heisenberg B →* Module.End ℂ (Ymodel hp) where
  toFun :=   (LinearEquiv.conj (homY χ hp)) ∘ (rho B χ)
  map_one' := by ext f y; simp [LinearEquiv.conj]
  map_mul' := by
    intro w v
    ext f z
    unfold homY; unfold rho; unfold rho_aux
    simp [_root_.map_mul, LinearEquiv.conj, Heisenberg.inv_def]
    rw [← mul_assoc]
    congr 2
    rw [← mul_inv_rev]
    norm_cast
    rw [← MonoidHom.map_mul χ]
    congr 2
    simp [Heisenberg.mul_def]
    constructor
    · rw [X_coor_add_Y B hp (-v.1) _ _ (by simp)]
      simp [X_coor]
      have := (XY_coor_linear B hp (-v.1) (-w.1 + z)).1
      simp [Heisenberg.mul_def, ← add_assoc (-v.1), X_coor] at this
      exact this
    · rw [X_coor_add_Y B hp (-v.1) _ _ (by simp)]
      simp [XY_coor]
      rw [Y_coor_add_Y B hp (-v.1), add_comm (-B w.1 v.1), add_assoc (-v.2 + -w.2)]
      have eq1 : -B w.1 v.1 + B (w.1 + v.1) (w.1 + v.1) = B w.1 w.1 + B v.1 w.1 + B v.1 v.1 := by
        simp [IsBilinear.llinear, IsBilinear.rlinear]
        rw [add_comm (B w.1 w.1), ← add_assoc, ← add_assoc (-B w.1 v.1), neg_add_cancel, zero_add, add_assoc]
      rw [eq1]
      let u := - w.2 + B w.1 w.1 + B (-w.1) z
      rw [add_sub _ u _, ← add_sub_right_comm _ u _, add_assoc _ _ u, add_comm _ u, ← add_assoc _ u _, sub_add, sub_sub]
      have eq2 : -v.2 + -w.2 + (B w.1 w.1 + B v.1 w.1 + B v.1 v.1) + B (-v.1 + -w.1) z = -v.2 + B v.1 v.1 + u + (B v.1 w.1 + B (-v.1) z) := by
        simp [u, IsBilinear.llinear, add_assoc]
        rw [add_comm (B (-v.1) z)]
        simp [← add_assoc]
        rw [add_comm _ (B v.1 v.1), add_assoc _ (B (-w.1) z) (B v.1 w.1), add_comm (B (-w.1) z) (B v.1 w.1)]
        simp [add_assoc]
      rw [eq2]
      simp [← add_sub]
      rw [← (XY_coor_linear' B hp (-v.1) (-w.1 + z)).2, ← add_assoc (-v.1) (-w.1) z, add_sub]
      have eq3 : B v.1 w.1 + B (-v.1) z = B (-v.1) (Y_coor B hp (-w.1 + z)) + B (-v.1) (X_coor B hp (-w.1 + z)) := by
        rw [B_neg_neg B v.1 w.1, ← IsBilinear.rlinear, ← IsBilinear.rlinear, add_comm ((Y_coor B hp (-(w.1,(0 : K)) + ((z : V), 0))) : V)]
        have := element_XY B hp ((-w.1, 0) + ((z : V),0))
        simp at this
        simp [← this]
      rw [eq3, add_sub_right_comm, add_assoc (-v.1), (XY_coor_linear' B hp (-v.1) _).1]
      have eq4 : B (Y_coor B hp (-v.1 + (-w.1 + z), 0)) ((X_coor B hp (-v.1, 0)) + ((X_coor B hp (-w.1 + z, 0)))) = B (Y_coor B hp (-v.1 + (-w.1 + z), 0)) (X_coor B hp (-v.1, 0)) + B (Y_coor B hp (-v.1, 0)) ((X_coor B hp (-w.1 + z, 0))) + B (Y_coor B hp (-w.1 + z, 0)) (X_coor B hp (-w.1 + z, 0)):= by
        simp [IsBilinear.rlinear, add_assoc]
        rw [(XY_coor_linear' B hp (-v.1) _).2]
        simp [IsBilinear.llinear]
      rw [eq4]
      simp [sub_add, ← add_sub, add_assoc]
      rw [add_sub, add_comm]
      simp [← add_sub]
      have eq5 : B (Y_coor B hp (-v.1, 0)) (X_coor B hp (-w.1 + ↑z, 0)) - B (-v.1) (X_coor B hp (-w.1 + ↑z, 0)) = -B (X_coor B hp (-v.1, 0)) (X_coor B hp (-w.1 + ↑z, 0)) := by nth_rw 2 [element_of_V_XY B hp (-v.1)]; simp [IsBilinear.llinear]
      rw [eq5]
      simp [sub_eq_add_neg]
    simp [Heisenberg.mul_def, XY_coor]
    nth_rw 2 [Y_coor_add_Y]
    rw [add_assoc, ]
    have := (XY_coor_linear' B hp (-v.1) (-w.1 + z)).2
    norm_cast at this



local notation "ρ" => (rhoY hp χ)

-- Lemma 2.3 correct the expression on RHS
omit [Fintype K] [FiniteDimensional K V] in
lemma rhoY.eq (x : X) (y y': Y) (t:K) (f : Ymodel hp) : (rhoY hp χ) (⟨x+y,t⟩: Heisenberg B) f y'=  χ ⟨⟨x,t - B y y + B x y' - B y' x - B (x + y') y⟩,by simp [subXK, Set.prod]⟩ * f (y' - y):= by
  unfold rhoY; unfold homY; unfold rho; unfold rho_aux
  simp [Heisenberg.inv_def, Heisenberg.mul_def, LinearEquiv.conj, Y_coor_add_X, Y_coor_add_Y, XY_coor, Y_in_Y]
  norm_cast
  simp [add_comm ((-y) : V) ((-x): V), X_coor_add_Y, X_in_X]
  norm_cast
  have := Y_in_Y B hp (-y : V) 0 (by simp)
  norm_cast at this
  rw [this]
  congr 2
  · rw [← MonoidHom.map_inv]
    congr
    have (w : Heisenberg B) (hw : w ∈ (subXK B X)): (⟨w, hw⟩ : (subXK B X))⁻¹ = ⟨w⁻¹, by simp_all [subXK, Set.prod]⟩ := by rfl
    rw [this]
    simp [Heisenberg.inv_def, ← sub_sub]
    rw [add_comm _ t]
    simp [IsBilinear.llinear, ← B_neg_neg B, IsBilinear.rlinear]
    rw [← add_sub, add_comm (B x x + B x y), ← sub_add_eq_add_sub (B y x)]
    simp [← sub_sub, ← add_assoc, add_sub]
    rw [add_comm _ (B x x)]
    simp [sub_eq_add_neg, ← add_assoc]
    rw [add_assoc (B x x), add_comm (B x x), add_assoc _ (B x x) _]
    simp [add_assoc]
    have  (w v : V) : B (-w) v = -B w v ∧ B w (-v) = -B w v := by
      constructor
      · rw [← neg_one_smul K]
        simp only [IsBilinear.lslinear]
        simp
      · rw [← neg_one_smul K]
        simp only [IsBilinear.rslinear]
        simp
    simp [this, ← add_assoc]
    rw [add_comm (- B x y), add_comm _ (B x y')]
    simp [add_assoc]
    have := hp.3 y y'
    simp [alternatingform] at this
    rw [sub_eq_zero] at this
    rw [this, ← neg_one_smul K, CharTwo.neg_eq]
    simp
  · rw [add_comm, sub_eq_add_neg]

omit [Fintype K] [FiniteDimensional K V] char2 in
lemma rhoY.eq' : ρ ((w,t) : Heisenberg B) = (χ₀ t) • ρ w := by
  unfold rhoY; unfold homY; unfold rho; unfold rho_aux
  ext f y
  simp [LinearEquiv.conj]
  simp only [XY_coor_linear]
  have := (XY_coor_linear B hp (w,t)⁻¹ (y,0)).2
  norm_cast at this
  simp only [this]
  have := (XY_coor_linear B hp (w,0)⁻¹ (y,0)).2
  norm_cast at this
  simp only [this]
  simp [Heisenberg.inv_def, XY_coor, Heisenberg.mul_def]
  rw [← smul_mul_assoc]
  congr 2
  have (x : ℂˣ) (y : ℂ) : x • y = x * y := by rfl
  rw [this]
  have := (isextendchara).1 t
  rw [← this]
  norm_cast
  rw [← MonoidHom.map_inv, ← MonoidHom.map_inv]
  have (w : Heisenberg B) (hw : w ∈ (subXK B X)): (⟨w, hw⟩ : (subXK B X))⁻¹ = ⟨w⁻¹, by simp_all [subXK, Set.prod]⟩ := by rfl
  simp [this, Heisenberg.inv_def]
  rw [← MonoidHom.map_mul χ]
  simp [Heisenberg.mul_def]
  congr 2
  simp [Y_in_Y, X_coor_of_Y, ← add_assoc]
  simp [← sub_sub, add_comm _ t, add_sub, add_sub]


variable {B} in
def rhoY.map_mul (h h' : Heisenberg B):  ρ h * ρ h' =  ρ (h * h') := by simp only [_root_.map_mul]

end Heisenberg_Representation
