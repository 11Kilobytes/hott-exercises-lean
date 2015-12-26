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

  definition rec_pair {C : Type} (c₀ : C) (cS : ℕ → C → C) (n : ℕ) : ℕ × C :=
    iter (0, c₀) (λ x, (succ (pr₁ x), cS (pr₁ x) (pr₂ x))) n

  definition rec' {C : Type} (c₀ : C) (cS : ℕ → C → C) (n : ℕ) : C := pr₂ (rec_pair c₀ cS n)

  definition rec_comp₁ {C : Type} (c₀ : C) (cS : ℕ → C → C) : rec' c₀ cS 0 = c₀ := rfl

  lemma rec_pr₁ {C : Type} (c₀ : C) (cS : ℕ → C → C) : Π (n : ℕ), pr₁ (rec_pair c₀ cS n) = n
  | rec_pr₁ 0 := rfl
  | rec_pr₁ (succ n) :=
    calc pr₁ (rec_pair c₀ cS (succ n)) = pr₁ (succ (pr₁ (rec_pair c₀ cS n)), cS (pr₁ (rec_pair c₀ cS n)) (pr₂ (rec_pair c₀ cS n))) : rfl
                                ... = succ (pr₁ (rec_pair c₀ cS n)) : rfl
                                ... = succ n : ap succ (rec_pr₁ n)

  definition rec_comp₂ {C : Type} (c₀ : C) (cS : ℕ → C → C) : Π (n : ℕ), rec' c₀ cS (succ n) = cS n (rec' c₀ cS n)
  | rec_comp₂ 0 := rfl
  | rec_comp₂ (succ n) :=
    calc rec' c₀ cS (succ (succ n)) = pr₂ (rec_pair c₀ cS (succ (succ n))) : rfl
                                ... = pr₂ (succ (pr₁ (rec_pair c₀ cS (succ n))), cS (pr₁ (rec_pair c₀ cS (succ n))) (pr₂ (rec_pair c₀ cS (succ n)))) : rfl
                                ... = cS (pr₁ (rec_pair c₀ cS (succ n))) (pr₂ (rec_pair c₀ cS (succ n))) : rfl
                                ... = cS (succ n) (pr₂ (rec_pair c₀ cS (succ n))) : rec_pr₁ c₀ cS (succ n)
                                ... = cS (succ n) (rec' c₀ cS (succ n)) : rfl

  definition exp : ℕ → ℕ → ℕ
  | exp x 0 := 1
  | exp x (succ n) := x * exp x n

  definition exp' : ℕ → ℕ → ℕ := function.flip (nat.rec (λ n, 1) (λ n f x, x * f x))

  definition add_zero (a : ℕ) : a + 0 = a := refl a

  definition zero_add  : Π (a : ℕ), 0 + a = a
  | zero_add 0 := refl 0
  | zero_add (succ n) := ap succ (zero_add n)

  theorem add_assoc : Π (a b c : ℕ), (a + b) + c = a + (b + c)
  | add_assoc a b 0 := refl (nat.rec a (λ x, succ) b)
  | add_assoc a b (succ n) :=
    calc (a + b) + (succ n) = succ ((a + b) + n) : rfl
                        ... = succ (a + (b + n)) : ap succ (add_assoc a b n)
                        ... = a + (succ (b + n)) : rfl
                        ... = a + (b + (succ n)) : rfl


  theorem add_assoc' : Π (a b c : ℕ), (a + b) + c = a + (b + c)
  | add_assoc' a b :=
   nat.rec (refl (nat.rec a (λ x, succ) b))
           (λ c ind_h, ap succ ind_h)


  print algebra.semiring

end nat
