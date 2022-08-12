/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathbin.Analysis.InnerProductSpace.Basic
import Mathbin.Analysis.SpecialFunctions.Complex.Arg

/-!
# Rays in the complex numbers

This file links the definition `same_ray ℝ x y` with the equality of arguments of complex numbers,
the usual way this is considered.

## Main statements

* `complex.same_ray_iff` : Two complex numbers are on the same ray iff one of them is zero, or they
  have the same argument.
* `complex.abs_add_eq/complex.abs_sub_eq`: If two non zero complex numbers have different argument,
  then the triangle inequality becomes strict.

-/


variable {x y : ℂ}

namespace Complex

theorem same_ray_iff : SameRay ℝ x y ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
    
  rcases eq_or_ne y 0 with (rfl | hy)
  · simp
    
  simp only [← hx, ← hy, ← false_orₓ, ← same_ray_iff_norm_smul_eq, ← arg_eq_arg_iff hx hy]
  field_simp [← hx, ← hy]
  rw [mul_comm, eq_comm]

theorem abs_add_eq_iff : (x + y).abs = x.abs + y.abs ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg :=
  same_ray_iff_norm_add.symm.trans same_ray_iff

theorem abs_sub_eq_iff : (x - y).abs = abs (x.abs - y.abs) ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg :=
  same_ray_iff_norm_sub.symm.trans same_ray_iff

theorem same_ray_of_arg_eq (h : x.arg = y.arg) : SameRay ℝ x y :=
  same_ray_iff.mpr <| Or.inr <| Or.inr h

theorem abs_add_eq (h : x.arg = y.arg) : (x + y).abs = x.abs + y.abs :=
  (same_ray_of_arg_eq h).norm_add

theorem abs_sub_eq (h : x.arg = y.arg) : (x - y).abs = ∥x.abs - y.abs∥ :=
  (same_ray_of_arg_eq h).norm_sub

end Complex

