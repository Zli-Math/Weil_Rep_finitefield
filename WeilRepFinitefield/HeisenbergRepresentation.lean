import WeilRepFinitefield.Heisenberg

/-!
# Schrödinger 函数模型与 Heisenberg 表示

先给出带特征等变条件的函数空间及模结构，再构造平移表示、Y 上的函数模型和坐标公式。
本文件合并原 SchrodingerModel 与 HeisenbergRepresentation，保留命名空间与数学定义。
Y 模型同构及部分算子公式仍含原有 sorry，不能视为已经完成的证明。
-/

noncomputable section Schrodinger_Model

open Function
open LinearMap.BilinForm


namespace  Schrodinger_Model

variable {K : Type } [hfK : Field K]  {V : Type } [hcV : AddCommGroup V] [hmV : Module K V]
(B : LinearMap.BilinForm K V)

local notation "B_s" => (B.toAlt)

/- This definition is not correct
structure polarization (X Y: Submodule K V) where
dimX : Module.finrank K X * 2 = Module.finrank K V
dualXY : Y ≃ₗ[K] Module.Dual K X
mul_zero : ∀ x : X, ∀ y : Y,  B_s x.1 y.1 = 0
-/


variable {X Y : Submodule K V} (hp : B.Polarization X Y)
variable {R : Type*} [Field R]

variable  (χ₀ : AddChar K R)

class extendcharacter (χ : (B.toSubgroup X)→* Rˣ) where
  equalχ₀ : ∀ y, χ ⟨(0, y), by simp [LinearMap.BilinForm.Heisenberg,LinearMap.BilinForm.toSubgroup,Set.prod] ⟩ = χ₀ y
--χ takes values in {1, -1, i, -i}

variable (χ : (B.toSubgroup X) →* Rˣ) [isextendchara : extendcharacter B χ₀ χ] (x : X)

def Schrodinger_model := {f : B.Heisenberg → R | ∀ h : B.Heisenberg, ∀ x: B.toSubgroup X ,f (h * x) = (χ x)⁻¹ * f (h)}

local notation "Sch" => Schrodinger_model B χ

lemma ext (f g : Sch) : (∀ h, f.1 h = g.1 h) → f = g:= by
  intro h; ext; simp [h]

lemma Sch_act_mem (h1 : f ∈ Sch)(h : B.Heisenberg) : (fun g => f (h * g)) ∈ Sch := by
  intro h' x
  calc
  _ =  f (h * (h' *x)) := by rfl
  _ =  f ((h * h') *x) := by group
  _ = (χ x)⁻¹ * f (h * h') := h1 (h * h') x

lemma Sch_add_mem (h1 : f1 ∈  Schrodinger_model B χ) (h2 : f2 ∈ Schrodinger_model B χ): f1 + f2 ∈ Schrodinger_model B χ := by
  simp_all [Heisenberg,Schrodinger_model]
  intro a b x y hxy
  rw [← mul_add]

lemma Sch_zero_mem : 0 ∈ Schrodinger_model B χ := by simp [Schrodinger_model]

lemma Sch_smul_mem (r : R ) (f : B.Heisenberg → R): f ∈  Schrodinger_model B χ → r • f ∈  Schrodinger_model B χ := by
  intro hf
  simp_all [Heisenberg,Schrodinger_model]
  intro a b x y hxy
  simp [mul_assoc, mul_comm]

instance instSubmodule: Submodule R (B.Heisenberg → R) where
  carrier := Schrodinger_model B χ
  add_mem' := Sch_add_mem B χ
  zero_mem' := Sch_zero_mem B χ
  smul_mem' := Sch_smul_mem B χ

instance instAddCommMonoid: AddCommMonoid (Schrodinger_model B χ) := Submodule.addCommMonoid (instSubmodule B χ)

instance : AddCommGroup (Schrodinger_model B χ) := Submodule.addCommGroup (instSubmodule B χ)

instance : Module R (Schrodinger_model B χ) := Submodule.module (instSubmodule B χ)

instance : Ring  (Module.End R (Schrodinger_model B χ)):= inferInstance

end Schrodinger_Model
end Schrodinger_Model

/-! ## 表示及 Y 坐标模型 -/

section Heisenberg_Representation
open Schrodinger_Model Function

set_option maxHeartbeats 400000

variable {K : Type } [hfK : Field K] {V : Type } [hcV : AddCommGroup V] [hmV : Module K V] (B : LinearMap.BilinForm K V) {X Y : Submodule K V}

variable {R : Type*} [Field R] (χ₀ : AddChar K R) (P: B.Polarization X Y) (χ : (B.toSubgroup X) →* Rˣ) [isextendchara : extendcharacter B χ₀ χ] (x : X) [char2: CharP K 2]


namespace LinearMap.BilinForm

open Heisenberg

abbrev rho_aux (h : B.Heisenberg) : Module.End R (Schrodinger_model B χ)
  where
  toFun := fun f => ⟨fun h2 => f.1 (h⁻¹ * h2), Sch_act_mem B χ f.2 h⁻¹⟩
  map_add' := by
    intro f1 f2
    ext h'
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



def rho : B.Heisenberg  →* Module.End R (Schrodinger_model B χ) where
  toFun := rho_aux B χ
  map_one' := by unfold rho_aux; simp ; rfl
  map_mul' := by
    intro a b
    ext f y
    unfold rho_aux
    simp only [Heisenberg.mul_def, Heisenberg.inv_def, neg_add_rev, map_add, LinearMap.add_apply, map_neg,
      LinearMap.neg_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mul_apply, neg_neg]
    apply congr_arg
    abel_nf

open LinearMap
open BilinForm

variable {B} (R) in
abbrev Polarization.Ymodel (P : Polarization B X Y):= Y → R

variable {B} in
def Polarization.homY : (Schrodinger_model B χ) ≃ₗ[R] (P.Ymodel R) where
  toFun := fun f => (fun y => f.1 y)
  map_add' := by intro a b; simp; rfl
  map_smul' := by intro m n; simp; rfl
  invFun := fun g => (⟨fun (w : Heisenberg B) => χ (⟨((P.X_coor w).1, w.2 - B (P.Y_coor  w).1 (P.X_coor w).1 ), by simp only [Heisenberg,
    toSubgroup, Set.prod, AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
    Submodule.mem_toAddSubmonoid, Set.mem_univ, and_true, eq_mpr_eq_cast, cast_eq, Subgroup.mem_mk,
    Set.mem_setOf_eq, SetLike.coe_mem]⟩)⁻¹ * g ⟨(P.Y_coor w).1, by simp⟩, by
    simp only [Heisenberg,Schrodinger_model, Units.val_inv_eq_inv_val, Subtype.forall, Prod.forall, map_inv,
      Subtype.coe_eta, Set.mem_setOf_eq]
    intro a b w t w₀
    have hw : w ∈ X := by simp [LinearMap.BilinForm.toSubgroup, Set.prod] at w₀; exact w₀
    simp only [Heisenberg,P.XY_coor_linear, map_add, LinearMap.add_apply]
    rw [← mul_assoc, ← mul_inv_rev]
    norm_cast
    sorry
    /-
    rw [← MonoidHom.map_mul χ]
    simp [Heisenberg.mul_def]
    norm_cast
    have hB : B a w - B (P.Y_coor (a, b) + P.Y_coor (w, t)) ((P.X_coor (a,b)).1 + w)  = B (P.X_coor (a,b)).1 w - B (P.X_coor (a,b)).1 (P.Y_coor (a, b)).1 := by
      have hab : a = (P.X_coor (a,b)).1 + (P.Y_coor (a,b)).1 := by
        have := P.element_XY (a,b)
        simp [Set.prod] at this
        exact this
      nth_rw 1 [hab]
      simp only [map_add, LinearMap.add_apply]
      rw [P.Y_coor_of_X hw]
      norm_cast
      simp_rw [Blzero,add_zero]
      abel_nf
      sorry
    -/
      /-
      have:= P.5
      simp [alternatingform] at this
      rw [← sub_eq_zero]
      apply this _ _ _ _
      simp
      simp
    simp [← add_sub (b + t), P.Y_coor_add_X  hw]
    --simp [P.Y_coor]
    have hw' := P.X_in_X _ t hw
    have hw'' := P.Y_coor_of_X (t:=t)  hw
    congr 2
    congr 2
    congr 2
    sorry
    sorry
    -/
    /-
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
      simp
     -/
      ⟩)
  left_inv := by
    simp [LeftInverse]
    intro f hf
    ext w
    symm
    nth_rw 1 [P.element_XY' w]
    simp only [Heisenberg, Schrodinger_model, Units.val_inv_eq_inv_val, Subtype.forall, Prod.forall,
      Set.mem_setOf_eq] at hf
    have := hf (P.Y_coor w) 0 (P.X_coor  w) (w.2 - B (P.Y_coor  w) (P.X_coor w))
    apply this
  right_inv := by
    simp only [Function.RightInverse, LeftInverse, zero_sub, map_inv, Units.val_inv_eq_inv_val,
      Subtype.coe_eta]
    intro g
    ext y
    have : P.Y_coor  (y,0) = y := by
      have hY := P.Y_in_Y y 0 (by simp)
      norm_cast at hY
    rw [this, P.X_coor_of_Y]
    have : B y (0 : X) = 0 := by
      norm_cast
      rw [Brzero B y]
    rw [← neg_eq_zero] at this
    simp only [this]
    have := χ.map_one'
    have one : (1 : B.toSubgroup X) = ⟨((0 : X), (0 : K)), by simp [Heisenberg,LinearMap.BilinForm.toSubgroup, Set.prod]⟩ := by rfl
    have h2 := χ.toFun_eq_coe
    rw [one, h2] at this
    rw [this]
    norm_cast
    rw [inv_one]
    norm_cast
    rw [one_mul]
    simp

variable {B} in
def Polarization.rhoY : Heisenberg B →* Module.End R (P.Ymodel R) where
  toFun :=   (LinearEquiv.conj (P.homY χ)) ∘ (rho B χ)
  map_one' := by ext f y; simp [LinearEquiv.conj]
  map_mul' := by
    intro w v
    ext f z
    unfold Polarization.homY; unfold rho; unfold rho_aux
    simp [_root_.map_mul, LinearEquiv.conj, Heisenberg.inv_def]
    rw [← mul_assoc]
    congr 2
    rw [← mul_inv_rev]
    norm_cast
    rw [← MonoidHom.map_mul χ]
    congr 2
    simp [Heisenberg.mul_def]
    sorry
    sorry
    /-
    constructor
    · rw [P.X_coor_add_Y (-v.1) _ _ (by simp)]
      simp [P.X_coor]
      have := (P.XY_coor_linear (-v.1) (-w.1 + z)).1
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
    simp [Heisenberg.mul_def, P.XY_coor]
    nth_rw 2 [P.Y_coor_add_Y]
    rw [add_assoc, ]
    have := (P.XY_coor_linear' (-v.1) (-w.1 + z)).2
    norm_cast at this
    -/



local notation "ρ" => (P.rhoY χ)

-- Lemma 2.3 correct the expression on RHS
variable {B} in
lemma Polarizatiion.rhoY.eq (x : X) (y y': Y) (t:K) (f : P.Ymodel R) : (P.rhoY χ) (⟨x+y,t⟩: Heisenberg B) f y'=  χ ⟨⟨x,t - B y y + B x y' - B y' x - B (x + y') y⟩,by simp [Heisenberg,LinearMap.BilinForm.toSubgroup, Set.prod]⟩ * f (y' - y):= by
  unfold Polarization.rhoY; unfold Polarization.homY; unfold rho; unfold rho_aux
  simp [Heisenberg.inv_def, Heisenberg.mul_def, LinearEquiv.conj, P.Y_coor_add_X, P.Y_coor_add_Y, P.XY_coor, P.Y_in_Y]
  norm_cast
  simp [add_comm ((-y) : V) ((-x): V), P.X_coor_add_Y, P.X_in_X]
  norm_cast
  have := P.Y_in_Y (-y : V) 0 (by simp)
  norm_cast at this
  rw [this]
  congr 2
  sorry
  sorry
  /-
  · rw [← MonoidHom.map_inv]
    congr
    have (w : Heisenberg B) (hw : w ∈ (B.toSubgroup X)): (⟨w, hw⟩ : (B.toSubgroup X))⁻¹ = ⟨w⁻¹, by simp_all [LinearMap.BilinForm.toSubgroup, Set.prod]⟩ := by rfl
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
    -/

lemma Polarization.rhoY.eq' : ρ ((w,t) : Heisenberg B) = (χ₀ t) • ρ w := by
  unfold Polarization.rhoY; unfold homY; unfold rho; unfold rho_aux
  ext f y
  simp [LinearEquiv.conj]
  simp only [XY_coor_linear]
  have := (P.XY_coor_linear  (w:=(w,t)⁻¹) (v:=(y,0))).2
  norm_cast at this
  simp only [this]
  have := (P.XY_coor_linear  (w:=(w,0)⁻¹) (v:=(y,0))).2
  norm_cast at this
  simp only [this]
  simp [Heisenberg.inv_def, XY_coor, Heisenberg.mul_def]
  sorry
  /-
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
  -/


variable {B} in
def Polarization.rhoY.map_mul (h h' : Heisenberg B):  ρ h * ρ h' =  ρ (h * h') := by simp only [_root_.map_mul]

end LinearMap.BilinForm

end Heisenberg_Representation
