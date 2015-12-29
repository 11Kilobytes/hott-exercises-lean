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
open sigma.ops
open prod
open prod.ops
open eq

section ex2
  definition sigma_rec {A : Type} {B : A → Type} {C : Type} (f : Π (a : A), B(a) → C) (p : Σ (x : A), B x) :  C :=
  f (pr₁ p) (pr₂ p)

  theorem sigma_comp {A : Type} {B : A → Type} {C : Type} (f : Π (a : A), B(a) → C) (a : A) (p : B a) : sigma_rec f ⟨a, p⟩ = (f a p) :=
  rfl
end ex2

section ex3
  definition prod_rec {A : Type} {B : Type} {C : Type} (f : A → B → C) (p : A × B) : C :=
  f (pr₁ p) (pr₂ p)

  definition prod_comp {A : Type} {B : Type} {C : Type} (f : A → B → C) (a : A) (b : B) : prod_rec f (a, b) = (f a b) :=
  rfl

end ex3

namespace nat
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

  section ex8
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
                                ... = a * b + ((b + 1) + a) : add_assoc b 1 a
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
    nat.rec_on a
      (show 0 * (b + c) = 0 * b + 0 * c, from
        calc 0 * (b + c) = 0 : (zero_mul (b + c))
                    ... = 0 + 0 : rfl
                    ... = 0 * b + 0 : { (zero_mul b)⁻¹ }
                    ... = 0 * b + 0 * c : { (zero_mul c)⁻¹ })
      (take a,
        assume IH : a * (b + c) = a * b + a * c,
        show (succ a) * (b + c) = (succ a) * b + (succ a) * c, from
          calc (succ a) * (b + c) = (b + c) * (succ a) : mul_comm (succ a) (b + c)
                             ... = b * (succ a) + c * (succ a) : right_distrib b c (succ a)
                             ... = (succ a) * b + c * (succ a) : { mul_comm b (succ a) }
                             ... = (succ a) * b + (succ a) * c : { mul_comm c (succ a) })

    theorem mul_assoc : Π (a b c : ℕ), (a * b) * c = a * (b * c)
    | mul_assoc a b 0 := proof rfl qed
    | mul_assoc a 0 c :=
      calc (a * 0) * c = 0 * c : rfl
                   ... = 0 : zero_mul c
                   ... = a * 0 : rfl
                   ... = a * (0 * c) : { (zero_mul c)⁻¹ }
    | mul_assoc 0 b c :=
      calc (0 * b) * c = 0 * c : { zero_mul b }
                   ... = 0 : zero_mul c
                   ... = 0 * (b * c) : (zero_mul (b * c))⁻¹
    | mul_assoc (succ a) (succ b) (succ c) :=
      calc ((succ a) * (succ b)) * (succ c) = ((succ a) * b + (succ a)) * (succ c) : rfl
                                         ... = (((succ a) * b) * (succ c)) + (succ a) * (succ c) : right_distrib ((succ a) * b) (succ a) (succ c)
                                         ... = (succ a) * (b * (succ c)) + (succ a) * (succ c): { mul_assoc (succ a) b (succ c) }
                                         ... = (succ a) * ((b * (succ c)) + (succ c)) : { (left_distrib (succ a) (b * (succ c)) (succ c))⁻¹ }
                                         ... = (succ a) * (((succ c) * b) + (succ c)) : { mul_comm b (succ c) }
                                         ... = (succ a) * ((succ c) * (succ b)) : rfl
                                         ... = (succ a) * ((succ b) * (succ c)) : { mul_comm (succ c) (succ b) }

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
end nat
