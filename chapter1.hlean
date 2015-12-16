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

  definition sigma_comp {A : Type} {B : A → Type} {C : Type} (f : Π (a : A), B(a) → C) (a : A) (p : B a) : sigma_rec f ⟨a, p⟩ = (f a p) :=
  rfl
end ex2

section ex3
  definition prod_rec {A : Type} {B : Type} {C : Type} (f : A → B → C) (p : A × B) : C :=
  f (pr₁ p) (pr₂ p)

  definition prod_comp {A : Type} {B : Type} {C : Type} (f : A → B → C) (a : A) (b : B) : prod_rec f (a, b) = (f a b) :=
  rfl

end ex3

namespace nat

  definition exp : ℕ → ℕ → ℕ
  | exp x 0 := 1
  | exp x (n + 1) := x * exp x n

  definition exp' : ℕ → ℕ → ℕ := function.flip (nat.rec (λ n, 1) (λ n f x, x * f x))

  definition add_zero (a : ℕ) : a + 0 = a := refl a

  definition zero_add  : Π (a : ℕ), 0 + a = a
  | zero_add 0 := refl 0
  | zero_add (n + 1) := ap succ (zero_add n)

  theorem add_assoc : Π (a b c : ℕ), (a + b) + c = a + (b + c)
  | add_assoc a b 0 := refl (nat.rec a (λ x, succ) b)
  | add_assoc a b (c + 1) := ap succ (add_assoc a b c)

  theorem add_assoc' : Π (a b c : ℕ), (a + b) + c = a + (b + c)
  | add_assoc' a b :=
   nat.rec (refl (nat.rec a (λ x, succ) b))
           (λ c ind_h, ap succ ind_h)


  print algebra.semiring

end nat
