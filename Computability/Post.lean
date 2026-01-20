/-
theorem exists_low_simple_set (O : Set ℕ) : ∃ A:Set ℕ, simpleIn O A ∧ lowIn O A := by
  sorry

theorem posts_problem_solution (O : Set ℕ) : ∃ A:Set ℕ, CEin O A ∧ O<ᵀA ∧ A<ᵀO⌜ := by
  rcases (exists_low_simple_set O) with ⟨A,h0,h1⟩
  use A
  constructor
  · sorry
  constructor
  · exact simpleIn_above_oracle h0
  · exact low_below_K h1
-/
