import Mathlib


local notation:max "M2" => Matrix (Fin 2) (Fin 2) (ZMod 2)


local notation:max "V2" => Matrix (Fin 2) (Fin 1) (ZMod 2)

abbrev B1 : M2 := !![0,1; 0,0]
abbrev v1 : V2 := !![0; 1]

#eval B1 * v1
#eval v1.transpose * B1 * v1
#eval B1
#eval B1 * B1
#eval B1.transpose
#check Matrix.toExpr

instance aa: DecidableEq (Fin 2 → ZMod 2) := by infer_instance


instance aa': DecidableEq M2 := by infer_instance



@[simp]
lemma Matrix.transpose_fin_two {a b c d: α} : !![a,b;c,d].transpose =!![a,c;b,d] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp

example (a b c d: R) [CommRing R] : !![a,b;c,d].transpose * !![0,1;-1,0] * !![a,b;c,d] = !![0,a*d-b*c; b*c - a*d, 0] := by
  rw  [Matrix.transpose_fin_two,Matrix.mul_fin_two,Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals ring_nf

section Bilinear_Forms


abbrev Omega : M2 := !![0,1; -1,0]

#eval Omega

abbrev is_form_omega (B : M2) : Prop :=
   (B -  B.transpose) = Omega


abbrev quadratic_form (B : M2) : V2 → ZMod 2:= fun x =>
 ((x.transpose) * B * x) 0 0

abbrev is_orthogonal_transform (B : M2) : M2 → Prop := fun g =>
  ∀ x : V2, quadratic_form B x = quadratic_form B (g * x)

-- Proposition 4.5 part 1
#eval Finset.filter (is_orthogonal_transform !![1,1;0,1])  (Finset.univ)


abbrev all_B_forms : Finset M2 :=
Finset.filter is_form_omega (Finset.univ)

#eval all_B_forms

def Witt_index (B : M2) : ℕ :=
  let nil := Finset.filter (fun x => quadratic_form B x= 0) (Finset.univ : Finset $ Matrix (Fin 2) (Fin 1) (ZMod 2))
  Finset.card nil

#eval  Finset.image Witt_index all_B_forms

#eval Witt_index ![![1, 1], ![0, 1]]



#eval (Finset.univ : Finset M2)
#eval Finset.filter is_form_omega (Finset.univ)
