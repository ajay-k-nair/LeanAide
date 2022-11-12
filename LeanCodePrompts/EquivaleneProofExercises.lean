import Mathbin.All
import LeanCodePrompts.CheckParse


/-- Every prime that is `1` greater than a multiple of `4` can be expressed as the sum of two squares. -/
example : ∀ {p : ℕ}, p % 4 = 1 → Prime p → ∃ a b, a ^ 2 + b ^ 2 = p ↔ ∀ p : ℕ, Prime p → (p % 4 = 1) → ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := sorry

/-- The product of two numbers, each of which is the sum of four squares, is itself a sum of four squares. -/
example : ∀ {a b : ℤ},   ∃ x y z w,     a = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧ b = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 →       ∃ x y z w, a * b = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ↔ (let is_sum_of_four_squares : ℕ → Prop := λ n : ℕ => ∃ (a b c d : ℕ), n = a^2 + b^2 + c^2 + d^2;
  ∀ (x y : ℕ), is_sum_of_four_squares x → is_sum_of_four_squares y → is_sum_of_four_squares (x * y)) := sorry

/-- A ring with all elements idempotent is commutative. -/
example : ({R : Type u} → [inst : CommRing R] → (∀ (x : R), x * x = x) → CommRing R) = ({R : Type u} → [inst : CommRing R] → (∀ (x : R), x * x = x) → CommRing R) → True := sorry

/-- There are infinitely many pairs of primes that differ exactly by `2`. -/
example : ∀ (n : ℕ), ∃ p₁ p₂, Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ p₁ + 2 = p₂ ∧ 2 * n < p₂  := sorry

/-- Every finite division ring is a field. -/
example : (K : Type u) → [inst : DivisionRing K] → Fintype K → Field K  := sorry

/-- Every non-empty poset in which every chain has an upper bound contains a maximal element. -/
example : ∀ {α : Type u_1} {r : α → α → Prop} [inst : Preorder α],   (∀ (c : Set α) (a : IsChain r c), ∃ ub, ∀ (a : α), a ∈ c → r a ub) →     ∀ [inst : Nonempty α], ∃ m, ∀ (a : α), r m a → r a m  := sorry

/-- A group whose automorphism group is cyclic is Abelian. -/
example : ∀ {α : Type u} [inst : MulZeroClass α] [inst_1 : Groupₓ α], IsCyclic α → IsLieAbelian α  := sorry

/-- A uniformly continuous function of a uniformly continuous function is uniformly continuous. -/
example : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : UniformSpace α] [inst_1 : UniformSpace β]   [inst_2 : UniformSpace γ] {f : α → β} {g : β → γ},   UniformContinuous f → UniformContinuous g → UniformContinuous (g ∘ f)  := sorry

/-- A uniformly continuous function of a uniformly continuous function is uniformly continuous. -/
example : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : UniformSpace α] [inst_1 : UniformSpace β]   [inst_2 : UniformSpace γ] {f : α → β} {g : β → γ},   UniformContinuous f → UniformContinuous g → UniformContinuous (g ∘ f)  := sorry

/-- If a function from the unit interval to itself has a point of period three, then it has points of all positive periods. -/
example : ∀ {f : ℤ → ℤ}, (∃ x, Function.IsPeriodicPt f 3 x) → ∀ (n : ℕ), ∃ x, Function.IsPeriodicPt f n x  := sorry

/-- A terminal object in a category is unique up to unique isomorphism. -/
example : ∀ {C : Type u₁} [inst : CategoryTheory.Category C] [inst_1 : CategoryTheory.Limits.HasTerminal C] {T T' : C}   (t : CategoryTheory.Limits.IsTerminal T),   CategoryTheory.Limits.IsTerminal T' → CategoryTheory.IsIso (CategoryTheory.Limits.IsTerminal.from t T')  := sorry

/-- The sum of the cubes of two positive integers is never equal to the cube of a third integer. -/
example : ∀ (a b c : ℤ), a ^ 3 + b ^ 3 ≠ c ^ 3  := sorry

/-- If every element of a group `G` has order `2`, then every pair of elements of `G` commutes. -/
example : ∀ {G : Type u_1} [inst : Group G], (∀ (x : G), x ^ 2 = 1) → ∀ {x y : G}, Commute x y  := sorry

/-- The product of two consecutive natural numbers is even. -/
example : ∀ {p q : ℕ}, p = q + 1 → Even (p * q)  := sorry

/-- Every free group is torsion free. -/
example : ∀ (α : Type u), Monoidₓ.IsTorsionFree (FreeGroup α)  := sorry

/-- Every natural number greater than `1` is divisible by a prime number.  -/
example : ∀ {n : ℕ}, 1 < n → ∃ p, Nat.Prime p ∧ p ∣ n  := sorry

/-- A finite torsion-free group is trivial -/
example : ∀ {G : Type u} [inst : Groupₓ G] [inst_1 : Fintype G], Monoidₓ.IsTorsionFree G → Fintype.card G = 1  := sorry

/-- Every finite division ring is a field. -/
example : (K : Type u) → [inst : DivisionRing K] → Fintype K → Field K  := sorry



/-- Every surjective homomorphism from a finitely generated free group to itself is injective -/
example : ∀ {α : Type u_1} {β : Type u_2} [inst : Groupₓ α] [inst_1 : Groupₓ β] [inst_2 : Fintype α] [inst_3 : Fintype β]   {f : α → β}, IsGroupHom f → Function.Surjective f → Function.Injective f  := sorry

/-- Every positive even integer can be written as the sum of two primes. -/
example : ∀ {n : ℕ}, 0 < n → Even n → ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n  := sorry

/-- Every matrix satisfies its own characteristic polynomial. -/
example : ∀ {R : Type u} [inst : CommRingₓ R] [inst_1 : Nontrivial R] {n : Type w} [inst_2 : DecidableEq n] [inst_3 : Fintype n]   (M : Matrix n n R), AlgHom.toFun (Polynomial.aeval M) (Matrix.charpoly M) = 0  := sorry

/-- If the square of a number is even, the number itself is even. -/
example : ∀ {M : Type u} [inst : Semiring M] [inst_1 : DecidableEq M] (a : M), Even (a * a) → Even a  := sorry



/-- If every point of a subset of a topological space is contained in some open set, the subset itself is open. -/
example : ∀ {α : Type u} [inst : TopologicalSpace α] {s : Set α}, (∀ (x : α), x ∈ s → ∃ t, IsOpen t ∧ x ∈ t) → IsOpen s  := sorry

/-- Every non-identity element of a free group is of infinite order. -/
example : ∀ {α : Type u} [inst : DecidableEq α] {x : FreeGroup α}, x ≠ 1 → ¬IsOfFinOrder x  := sorry

/-- For any two relatively prime positive integers $a$ and $b$, every sufficiently large natural number $N$ can be written as a linear combination $ax + by$ of $a$ and $b$, where both $x$ and $y$ are natural numbers. -/
example : ∀ {m n : ℕ}, 0 < m → 0 < n → Nat.gcd m n = 1 → ∀ (N : ℕ), N > m * n → ∃ x y, N = m * x + n * y  := sorry

/-- Every field is a ring. -/
example : {α : Type u_1} → [inst : Field α] → Ring α  := sorry

/-- The set of units in a ring forms a group. -/
example : (R : Type u_1) → [inst : Ringₓ R] → AddGroup (Units R)  := sorry

/-- If the direct product of two groups is torsion free then each of the groups is torsion free. -/
example : ∀ {η : Type u_1} (G : Type u_2) [inst : Groupₓ G] {Γ : Type u_3} [inst_1 : Groupₓ Γ],   Monoidₓ.IsTorsionFree (G × Γ) → Monoidₓ.IsTorsionFree G ∧ Monoidₓ.IsTorsionFree Γ  := sorry

