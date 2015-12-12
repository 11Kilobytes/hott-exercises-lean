import algebra.ring
import function
open eq

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
