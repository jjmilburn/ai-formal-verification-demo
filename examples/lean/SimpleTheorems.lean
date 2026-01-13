/-
  Simple Theorems for LLM Proof Generation Demo

  These are small theorems that an LLM can prove in one or two tactics.
  We use these to demonstrate the verification loop without complex setup.
-/

-- Theorem 1: Addition is commutative
theorem add_comm_example : ∀ a b : Nat, a + b = b + a := by
  sorry  -- LLM should fill this

-- Theorem 2: Zero is identity for addition
theorem add_zero_right : ∀ n : Nat, n + 0 = n := by
  sorry  -- LLM should fill this

-- Theorem 3: Successor preserves equality
theorem succ_inj : ∀ a b : Nat, Nat.succ a = Nat.succ b → a = b := by
  sorry  -- LLM should fill this

-- Theorem 4: List append is associative
theorem append_assoc : ∀ (xs ys zs : List α), xs ++ ys ++ zs = xs ++ (ys ++ zs) := by
  sorry  -- LLM should fill this

-- Theorem 5: Length of appended lists
theorem length_append : ∀ (xs ys : List α), (xs ++ ys).length = xs.length + ys.length := by
  sorry  -- LLM should fill this

-- Theorem 6: Simple implication
theorem imp_self : ∀ P : Prop, P → P := by
  sorry  -- LLM should fill this

-- Theorem 7: And elimination
theorem and_left : ∀ P Q : Prop, P ∧ Q → P := by
  sorry  -- LLM should fill this

-- Theorem 8: Double negation (classical)
theorem double_neg : ∀ P : Prop, ¬¬P → P := by
  sorry  -- LLM should fill this
