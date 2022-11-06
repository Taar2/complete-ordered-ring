noncomputable theory

/- This one just proves that a ring with axioms r1-r15
   (actually, r1, r2, r12 and r15 are not nedded)
   and 0 ≠ 1, has 0 < 1.

   Constructive reasoning only.
-/

constant ordring : Type
notation `ℝ` := ordring

namespace ordring

constant zero : ordring

constant one : ordring

constant add (x y: ordring) : ordring

constant mul (x y: ordring) : ordring

constant neg (x: ordring) : ordring

constant lt (x y: ordring) : Prop

instance : has_zero ℝ := ⟨zero⟩
instance : has_one ℝ := ⟨one⟩
instance : has_add ℝ := ⟨add⟩
instance : has_neg ℝ := ⟨neg⟩
instance : has_mul ℝ := ⟨mul⟩
instance : has_lt ℝ := ⟨lt⟩

variables (x y z t u: ordring)

-- axiom r1: x < x → false

-- axiom r2: x < y → y < z → x < z

axiom r3: x < 0 ∨ 0 = x ∨ 0 < x

axiom r4: x < y → x + z < y + z

axiom r5: 0 < x → 0 < y → 0 < x * y

axiom r6: 0 + x = x

axiom r7: 0 * x = 0

axiom r8: 1 * x = x

axiom r9: x + y = y + x

axiom r10: x * y = y * x

axiom r11: x + y + z = x + (y + z)

-- axiom r12: x * y * z = x * (y * z)

axiom r13: x * (y + z) = x * y + x * z

axiom r14: x + (-x) = 0

-- axiom r15: ∀ (f: ℕ → ℝ), (∀ (n: ℕ), f n < f (n + 1)) → (∃ (A: ℝ), ∀ (n: ℕ), f n < A) → (∃ (L: ℝ), ∀ (ε: ℝ), 0 < ε → ∃ (N: ℕ), ∀ n, N < n → L + -ε < f n ∧ f n < L + ε)

axiom r16: (0: ℝ) ≠ 1

theorem zero_lt_one : (0: ℝ) < 1 :=
begin
  cases (r3 1) with h1 h1,
  have h2 := r4 _ _ (-1) h1,
  rw [r14, r6] at h2,
  have h3 := r5 _ _ h2 h2,
  have h4 : (-1) * (1 + -1) = (0: ℝ),
  rw [r14, r10, r7],
  rw [r13, r10 _ 1, r8] at h4,
  have h5 : 1 + (-1 + (-1) * -1) = (1: ℝ),
  rw [h4, r9, r6],
  rw [← r11, r14, r6] at h5,
  rw [h5] at h3,
  exact h3,
  cases h1 with h1 h1,
  exfalso, exact (r16 h1),
  assumption,
end

#print axioms zero_lt_one

end ordring
