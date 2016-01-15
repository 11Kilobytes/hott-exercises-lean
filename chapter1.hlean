-- Copyright 2015 Kabelo Moiloa

-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at

-- http://www.apache.org/licenses/LICENSE-2.0

-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

import algebra.ring
import function
open sigma
open prod
open eq

section ex2
  section sigma
    open sigma.ops
    variables {A : Type} {B : A → Type} {C : Type} (f : Π (a : A), B(a) → C)

    definition sigma_rec (p : Σ (x : A), B x) :  C :=
    f (pr₁ p) (pr₂ p)

    theorem sigma_comp (a : A) (p : B a) : sigma_rec f ⟨a, p⟩ = (f a p) :=
    rfl
  end sigma

  section prod
    open prod.ops
    variables {A : Type} {B : Type} {C : Type} (f : A → B → C)
    definition prod_rec (p : A × B) : C :=
    f (pr₁ p) (pr₂ p)

    definition prod_comp (a : A) (b : B) : prod_rec f (a, b) = (f a b) :=
    rfl
  end prod
end ex2

section ex3
  section sigma
    open sigma.ops
    variables {A : Type} {B : A → Type} {C : (Σ (x : A), B x) → Type} (f : Π (a : A) (b : B a), C ⟨a, b⟩)

    definition sigma_ind (p : Σ (x : A), B x) : C p :=
    (sigma.eta p) ▸ (f (pr₁ p) (pr₂ p))

    theorem sigma_ind_comp (a : A) (b : B a) : sigma_ind f ⟨a, b⟩ = (f a b) :=
    rfl
  end sigma

  section prod
    open prod.ops
    variables {A : Type} {B : Type} {C : A × B → Type} (f : Π (a : A) (b : B), C (a, b))

    definition prod_ind (p : A × B) : C p :=
    (prod.eta p) ▸ (f (pr₁ p) (pr₂ p))

    definition prod_ind_comp (a : A) (b : B) : prod_ind f (a, b) = (f a b) :=
    rfl
  end prod
end ex3


open prod.ops
open nat
definition iter {C : Type} (c₀ : C) (cS : C → C) : ℕ → C
| iter 0 := c₀
| iter (succ n) := cS (iter n)

section ex4
  variables {C : Type} (c₀ : C) (cS : ℕ → C → C)

  definition rec_pair : ℕ → ℕ × C :=
  iter (0, c₀) (λ x, (succ (pr₁ x), cS (pr₁ x) (pr₂ x)))

  definition rec' (n : ℕ) : C := pr₂ (rec_pair c₀ cS n)

  theorem rec_comp₁ : rec' c₀ cS 0 = c₀ := rfl

  lemma rec_pr₁ (n : ℕ) : pr₁ (rec_pair c₀ cS n) = n :=
  nat.rec_on n
    (show pr₁ (rec_pair c₀ cS 0) = 0, from rfl)
    (take n,
      assume IH : pr₁ (rec_pair c₀ cS n) = n,
      show (pr₁ (rec_pair c₀ cS (succ n)) = (succ n)), from
        calc pr₁ (rec_pair c₀ cS (succ n)) = pr₁ (succ (pr₁ (rec_pair c₀ cS n)), cS (pr₁ (rec_pair c₀ cS n)) (pr₂ (rec_pair c₀ cS n))) : rfl
                                        ... = succ (pr₁ (rec_pair c₀ cS n)) : rfl
                                        ... = succ n : ap succ IH)

  theorem rec_comp₂ (n : ℕ) : rec' c₀ cS (succ n) = cS n (rec' c₀ cS n) :=
  nat.rec_on n
    (show rec' c₀ cS (succ 0) = cS 0 (rec' c₀ cS 0), from rfl)
    (take n,
      assume IH : rec' c₀ cS (succ n) = cS n (rec' c₀ cS n),
      show rec' c₀ cS (succ (succ n)) = cS (succ n) (rec' c₀ cS (succ n)), from
        calc rec' c₀ cS (succ (succ n)) = pr₂ (rec_pair c₀ cS (succ (succ n))) : rfl
                                    ... = pr₂ (succ (pr₁ (rec_pair c₀ cS (succ n))), cS (pr₁ (rec_pair c₀ cS (succ n))) (pr₂ (rec_pair c₀ cS (succ n)))) : rfl
                                    ... = cS (pr₁ (rec_pair c₀ cS (succ n))) (pr₂ (rec_pair c₀ cS (succ n))) : rfl
                                    ... = cS (succ n) (pr₂ (rec_pair c₀ cS (succ n))) : { rec_pr₁ c₀ cS (succ n) }
                                    ... = cS (succ n) (rec' c₀ cS (succ n)) : { IH })
end ex4

section ex5
  open sigma.ops
  definition union.{u v} (A : Type.{u}) (B : Type.{v}) := Σ (x : bool), (@bool.rec_on.{(max u v) + 1} (λ x, Type.{max u v}) x (lift A) (lift B))
  notation A `+` B := union A B

  variables {A : Type} {B : Type}

  definition inl (a : A) : A + B := ⟨bool.ff, (lift.up a)⟩
  definition inr (b : B) : A + B := ⟨bool.tt, (lift.up b)⟩

  definition union_ind {C : A + B → Type} (rec_l : Π (a : A), C (inl a)) (rec_r : Π (b : B), C (inr b)) : Π (x : A + B), C x
  | union_ind ⟨bool.ff, a⟩ := (lift.up_down a) ▸ (rec_l (lift.down a))
  | union_ind ⟨bool.tt, b⟩ := (lift.up_down b) ▸ (rec_r (lift.down b))

  definition union_comp₁ {C : A + B → Type} (rec_l : Π (a : A), C (inl a)) (rec_r : Π (b : B), C (inr b)) (a : A) : (union_ind rec_l rec_r (inl a)) = (rec_l a) :=
  by reflexivity

  definition union_comp₂ {C : A + B → Type} (rec_l : Π (a : A), C (inl a)) (rec_r : Π (b : B), C (inr b)) (b : B) : (union_ind rec_l rec_r (inr b)) = (rec_r b) :=
  by reflexivity
end ex5

section ex6
  open sigma.ops
  definition product.{u v} (A : Type.{u}) (B : Type.{v}) := Π (x : bool), (@bool.rec_on.{(max u v) + 1} (λ x, Type.{max u v}) x (lift A) (lift B))
  notation A `×` B := product A B

  variables {A : Type} {B : Type}
  definition make_pair (a : A) (b : B) : A × B := (bool.rec (lift.up a) (lift.up b))

  definition proj₁ (p : A × B) : A := (lift.down (p bool.ff))
  definition proj₂ (p : A × B) : B := (lift.down (p bool.tt))

  definition product_eta (p : A × B) : (make_pair (proj₁ p) (proj₂ p)) = p :=
  eq_of_homotopy
    (take x : bool,
      bool.rec_on x
        (show (make_pair (proj₁ p) (proj₂ p) bool.ff) = (p bool.ff), from (lift.up_down (p bool.ff)))
        (show (make_pair (proj₁ p) (proj₂ p) bool.tt) = (p bool.tt), from (lift.up_down (p bool.tt))))

  definition product_ind {C : A × B → Type} (f : Π (a : A) (b : B), C (make_pair a b)) (p : A × B) : C p :=
  (product_eta p) ▸ (f (proj₁ p) (proj₂ p))

  definition product_comp {C : A × B → Type} (f : Π (a : A) (b : B), C (make_pair a b)) (a : A) (b : B) : (product_ind f (make_pair a b)) = (f a b) :=
  begin
    unfold [product_ind, product_eta, make_pair, lift.up_down, proj₁, proj₂],
    assert p : (λ x, bool.rec_on x (refl (lift.up a)) (refl (lift.up b))) = (λ x, refl (make_pair a b x)),
    apply eq_of_homotopy (bool.rec rfl rfl),
    unfold rfl,
    unfold make_pair at p,
    rewrite p, clear p,
    fold (make_pair a b),
    rewrite (eq_of_homotopy_idp (make_pair a b)),
  end
end ex6

section ex7
  open sigma.ops
  variables {A : Type} (a : A) {P : Π (x : A), a = x → Type} {d : P a (refl a)}

  definition contr_components (x y : A) (p : x = y) : ⟨x, (refl x)⟩ = ⟨y, p⟩ :=
  eq.rec_on' p (λ a, rfl)

  definition contr_path_space (a : A) (s : Σ (y : A), a = y) : ⟨a, (refl a)⟩ = s :=
  (sigma.eta s) ▸ contr_components a (pr₁ s) (pr₂ s)

  definition eq_ind (x : A) (p : a = x) : P x p :=
  transport (λ s, P (pr₁ s) (pr₂ s)) (contr_path_space a ⟨x, p⟩) d

  definition eq_comp : eq_ind a a (refl a) = a := rfl
end ex7

section ex8
  open nat
  definition exp : ℕ → ℕ → ℕ
  | exp x 0 := 1
  | exp x (succ n) := x * exp x n

  definition exp' : ℕ → ℕ → ℕ := function.flip (nat.rec (λ n, 1) (λ n f x, x * f x))

  theorem add_zero (a : ℕ) : a + 0 = a := rfl

  theorem zero_add  (a : ℕ) : 0 + a = a :=
  nat.rec_on a
    (show 0 + 0 = 0, from rfl)
    (take a,
      assume IH : 0 + a = a,
      show 0 + (succ a) = (succ a), from
        calc 0 + (succ a) = (succ (0 + a)) : rfl
                        ... = (succ a) : ap succ IH)

  theorem add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c) :=
  nat.rec_on c
    (show (a + b) + 0 = a + (b + 0), from rfl)
    (take n,
      assume IH : (a + b) + n = a + (b + n),
      show (a + b) + (succ n) = a + (b + (succ n)), from
        calc (a + b) + (succ n) = succ ((a + b) + n) : rfl
                              ... = succ (a + (b + n)) : ap succ IH
                              ... = a + (succ (b + n)) : rfl
                              ... = a + (b + (succ n)) : rfl)

  theorem one_add (a : ℕ) : (succ a) = 1 + a :=
  nat.rec_on a
    (show (succ 0) = 1 + 0, from rfl)
    (take a,
      assume IH : (succ a) = 1 + a,
      show (succ (succ a)) = 1 + (succ a), from
        calc (succ (succ a)) = (succ a) + 1 : rfl
                          ... = (1 + a) + 1 : { IH }
                          ... = 1 + (a + 1) : add_assoc 1 a 1
                          ... = 1 + (succ a) : rfl)

  theorem add_comm (a b : ℕ) : a + b = b + a :=
  nat.rec_on b
    (show a + 0 = 0 + a, from (zero_add a)⁻¹)
    (take b,
      assume IH : a + b = b + a,
      show a + (succ b) = (succ b) + a, from
        calc a + (succ b) = (succ (a + b)) : rfl
                        ... = (succ (b + a)) : ap succ IH
                        ... = 1 + (b + a) : one_add (b + a)
                        ... = (1 + b) + a : add_assoc 1 b a
                        ... = (succ b) + a : { (one_add b)⁻¹ })

  theorem one_mul (a : ℕ) : 1 * a = a :=
  nat.rec_on a
    (show 1 * 0 = 0, from rfl)
    (take a,
      assume IH : 1 * a = a,
      show 1 * (succ a) = (succ a), from
        calc 1 * (succ a) = (1 * a) + 1 : rfl
                        ... = a + 1 : { IH }
                        ... = (succ a) : rfl)

  theorem mul_one (a : ℕ) : a * 1 = a :=
    calc a * 1 = (a * 0) + a : rfl
            ... = 0 + a : rfl
            ... = a : zero_add a

  theorem zero_mul (a : ℕ) : 0 * a = 0 :=
  nat.rec_on a
    (show 0 * 0 = 0, from rfl)
    (take a,
      assume IH : 0 * a = 0,
      show 0 * (succ a) = 0, from
        calc 0 * (succ a) = 0 * a + 0 : rfl
                        ... = 0 + 0 : { IH }
                        ... = 0 : rfl)

  theorem mul_zero (a : ℕ) : a * 0 = 0 := rfl

  theorem right_distrib (a b c : ℕ) : (a + b) * c = a * c + b * c :=
  nat.rec_on c
    (show (a + b) * 0 = a * 0 + b * 0, from rfl)
    (take c,
      assume IH : (a + b) * c = a * c + b * c,
      show (a + b) * (succ c) = a * (succ c) + b * (succ c), from
        calc (a + b) * (succ c) = ((a + b) * c) + (a + b) : rfl
                              ... = (a * c + b * c) + (a + b) : { IH }
                              ... = a * c + (b * c + (a + b)) : { add_assoc (a * c) (b * c) (a + b) }
                              ... = a * c + (b * c + (b + a)) : { add_comm a b }
                              ... = a * c + ((b * c + b) + a) : { (add_assoc (b * c)  b a)⁻¹ }
                              ... = a * c + (b * (succ c) + a) : rfl
                              ... = a * c + (a + b * (succ c)) : { add_comm (b * (succ c)) a }
                              ... = (a * c + a) + b * (succ c) : (add_assoc (a * c) a (b * (succ c)))⁻¹
                              ... = a * (succ c) + b * (succ c) : rfl)

  lemma succ_mul (a b : ℕ) : (succ a) * b = a * b + b :=
  nat.rec_on b
    (show (succ a) * 0 = a * 0 + 0, from rfl)
    (take b,
      assume IH : (succ a) * b = a * b + b,
      show (succ a) * (succ b) = a * (succ b) + (succ b), from
        calc (succ a) * (succ b) = (succ a) * b + (succ a) : rfl
                              ... = (a * b + b) + (succ a) : { IH }
                              ... = a * b + (b + (succ a)) : add_assoc (a * b) b (succ a)
                              ... = a * b + (b + (1 + a)) : { one_add a }
                              ... = a * b + ((b + 1) + a) : { (add_assoc b 1 a)⁻¹ }
                              ... = a * b + ((succ b) + a) : rfl
                              ... = a * b + (a + (succ b)) : { add_comm (succ b) a }
                              ... = (a * b + a) + (succ b) : (add_assoc (a * b) a (succ b))⁻¹
                              ... = a * (succ b) + (succ b) : rfl)

  theorem mul_comm (a b : ℕ) : a * b = b * a :=
  nat.rec_on b
    (show a * 0 = 0 * a, from
      calc a * 0 = 0 : rfl
            ... = 0 * a : (zero_mul a)⁻¹)
    (take b,
      assume IH : a * b = b * a,
      show a * (succ b) = (succ b) * a, from
        calc a * (succ b) = a * b + a : rfl
                        ... = b * a + a : { IH }
                        ... = (succ b) * a : (succ_mul b a)⁻¹)


  theorem left_distrib (a b c : ℕ) : a * (b + c) = a * b + a * c :=
  nat.rec_on c
    (show a * (b + 0) = a * b + a * 0, by reflexivity)
    (take c,
      assume IH : a * (b + c) = a * b + a * c,
      show a * (b + (succ c)) =  a * b + a * (succ c), from
        calc a * (b + (succ c)) = a * (succ (b + c)) : rfl
                            ... = a * (b + c) + a : rfl
                            ... = (a * b + a * c) + a : { IH }
                            ... = a * b + (a * c + a) : add_assoc (a * b) (a * c) a
                            ... = a * b + a * (succ c) : rfl)

  theorem mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) :=
  nat.rec_on c
    (show (a * b) * 0 = a * (b * 0), by reflexivity)
    (take c,
      assume IH : (a * b) * c = a * (b * c),
      show (a * b) * (succ c) = a * (b * (succ c)), from
        calc (a * b) * (succ c) = (a * b) * c + a * b : rfl
                            ... = a * (b * c) + a * b : { IH }
                            ... = a * ((b * c) + b)   : { (left_distrib a (b * c) b)⁻¹ }
                            ... = a * (b * (succ c))  : rfl)

  definition semiring := {| algebra.semiring ℕ,
                            is_hset_carrier := is_hset_of_decidable_eq,
                            add := add,
                            mul := mul,
                            zero := 0,
                            add_zero := add_zero,
                            zero_add := zero_add,
                            add_comm := add_comm,
                            add_assoc := add_assoc,
                            one_mul := one_mul,
                            mul_one := mul_one,
                            zero_mul := zero_mul,
                            mul_zero := mul_zero,
                            left_distrib := left_distrib,
                            right_distrib := right_distrib,
                            mul_assoc := mul_assoc |}
end ex8
