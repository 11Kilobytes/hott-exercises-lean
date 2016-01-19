open eq

section ex1
  variables {A : Type} {x y z : A} (p : x = y) (q : y = z)

  definition concat₁ : x = z := eq.rec' (λ a z q, eq.rec' refl q) p z q

  definition concat₂ : x = z := eq.rec' (λ a z q, q) p z q

  definition concat₃ : x = z := eq.rec' (λ a z p, p) q z p

  notation x `·₁` y := concat₁ x y
  notation x `·₂` y := concat₂ x y
  notation x `·₃` y := concat₃ x y

  definition coh₁ : (p ·₁ q) = (p ·₂ q) := by induction p; induction q; reflexivity

  definition coh₂ : (p ·₂ q) = (p ·₃ q) := by induction p; induction q; reflexivity

  definition coh₃ : (p ·₃ q) = (p ·₁ q) := by induction p; induction q; reflexivity

  definition triangle : (coh₁ p q) ⬝ (coh₂ p q) = (coh₃ p q)⁻¹ :=
  by induction p; induction q; reflexivity
end ex1
