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
end ex1

section ex2
  variables {A : Type} {x y z : A} (p : x = y) (q : y = z)

  theorem triangle : (coh₁ p q) ⬝ (coh₂ p q) = (coh₃ p q)⁻¹ :=
  by induction p; induction q; reflexivity
end ex2

section ex3
  variables {A : Type} {x y z : A} (p : x = y) (q : y = z)

  definition concat₄ : x = z :=
  eq.rec' (λ a z, id) p z q

  notation x `·₄` y := concat₄ x y

  theorem coh₄₁ : (p ·₄ q) = (p ·₁ q) := by induction p; induction q; reflexivity

  theorem coh₄₂ : (p ·₄ q) = (p ·₂ q) := (coh₄₁ p q) ⬝ (coh₁ p q)

  theorem coh₄₃ : (p ·₄ q) = (p ·₃ q) := (coh₄₁ p q) ⬝ (coh₃ p q)⁻¹
end ex3

section ex4
  variables {A B : Type} {x y : A} (f : A → B) (p : x = y)

  definition precomp_tr_constant (q : f x = f y) : (p ▸ f x) = (f y) :=
  tr_constant p (f x) ⬝ q

  definition precomp_tr_constant_inv (q : p ▸ f x = f y) : f x = f y :=
  (tr_constant p (f x))⁻¹ ⬝ q

  definition is_equiv_precomp_tr_constant :=
  is_equiv.adjointify (precomp_tr_constant f p) (precomp_tr_constant_inv f p)
  (take q : p ▸ f x = f y,
    calc
      (precomp_tr_constant f p (precomp_tr_constant_inv f p q))
          = tr_constant p (f x) ⬝ ((tr_constant p (f x))⁻¹ ⬝ q)  : rfl
      ... = (tr_constant p (f x) ⬝ (tr_constant p (f x))⁻¹) ⬝ q  : by rewrite eq.con.assoc'
      ... = idp ⬝ q                                             :  by rewrite eq.con.right_inv
      ... = q                                                   : idp_con)
end ex4 
