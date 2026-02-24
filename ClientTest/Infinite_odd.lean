import Mathlib
universe u v w u_1 u_2 u_3 u₁ u₂ u₃
set_option maxHeartbeats 10000000
set_option linter.unreachableTactic false
open scoped Nat
theorem infinitely_many_odd : {n : ℕ | Odd n}.Infinite := by sorry

