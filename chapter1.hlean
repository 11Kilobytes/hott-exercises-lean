import algebra.ring
import function
open eq

namespace nat

  definition exp : ℕ → ℕ → ℕ
  | exp x 0 := 1
  | exp x (n + 1) := x * exp x n

  definition exp' : ℕ → ℕ → ℕ := function.flip (nat.rec (λ n, 1) (λ n f x, x * f x))



end nat
