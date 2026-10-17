import WeilRepFinitefield.Compute
import WeilRepFinitefield.QuadraticRing

/-!
# 有限例子的精确系数域

利用两次二次扩张表示 ℚ(√2,i)，定义 QQ 及相关记号、非平方性实例和平方根实例。
保留原来的 native_decide 用法；这里是计算例子的系数支持，不是新的 Weil 指数证明。
-/

section Quadratictwo

set_option quotPrecheck false

local notation:max "Q" => QuadraticRing (2 : ℚ)
abbrev QQ := QuadraticRing (-1 : Q)
local notation:max "QQ" => QuadraticRing (-1 : Q)
local notation "!QR[" a:70 "; " b:70 "; " c:70 "; " d:70 "]"   => (QuadraticRing.toQring
  (-1 : QuadraticRing (2:ℚ))
  (QuadraticRing.toQring (R := ℚ) (2:ℚ) (a) (b))
  (QuadraticRing.toQring (R := ℚ) (2:ℚ) (c) (d)))


instance : QuadraticRing.Nonsquare (2 : ℚ) where
  ns' := by
    intro n H
    have : ¬ IsSquare (2 : ℚ)  := by
      native_decide
    rw [IsSquare] at this
    push_neg at this
    exact this n H


instance : QuadraticRing.Nonsquare (-1 : Q) where
  ns' := by
    intro n H
    simp only [QuadraticRing.one_def, QuadraticRing.neg_def, neg_zero, QuadraticRing.mul_def,
      QuadraticRing.mk.injEq] at H
    replace H:= H.1
    have : (-1 :ℚ) < n.a*n.a + 2 * n.b * n.b := by
      calc
       _ < 0 := by decide
       _ ≤ n.a*n.a + 2 * n.b * n.b := by
        refine Rat.add_nonneg ?_ ?_
        · exact mul_self_nonneg n.a
        · rw [mul_assoc]
          refine Rat.mul_nonneg rfl ?_
          exact mul_self_nonneg n.b
    linarith


instance : HRadical 2 (2 : QQ) where
  r := !QR[0;1;0;0]
  hr := by native_decide

/-
#eval (⟨0,1⟩: Q) / (⟨1,1⟩:Q)
#eval ((!QR[0;1;0;0]) * (!QR[1;0;0;1]) :QQ)
#eval ((!QR[0;1;0;0]) * (!QR[1;0;0;1])⁻¹ :QQ)
#eval !QR[0;1;0;0] / !QR[1;0;0;1]

-/
end Quadratictwo
