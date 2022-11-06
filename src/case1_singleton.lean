/-
Copyright (c) 2022 Laurent Bonaventure. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurent Bonaventure
-/

noncomputable theory

/- This one just proves that a ring with axioms r1-r15
   (actually, only r7 and r8 are nedded)
   and 0 = 1, is a singleton.

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

axiom r1: x < x → false

axiom r2: x < y → y < z → x < z

axiom r3: x < 0 ∨ 0 = x ∨ 0 < x

axiom r4: x < y → x + z < y + z

axiom r5: 0 < x → 0 < y → 0 < x * y

axiom r6: 0 + x = x

axiom r7: 0 * x = 0

axiom r8: 1 * x = x

axiom r9: x + y = y + x

axiom r10: x * y = y * x

axiom r11: x + y + z = x + (y + z)

axiom r12: x * y * z = x * (y * z)

axiom r13: x * (y + z) = x * y + x * z

axiom r14: x + (-x) = 0

axiom r15: ∀ (f: ℕ → ℝ), (∀ (n: ℕ), f n < f (n + 1)) → (∃ (A: ℝ), ∀ (n: ℕ), f n < A) → (∃ (L: ℝ), ∀ (ε: ℝ), 0 < ε → ∃ (N: ℕ), ∀ n, N < n → L + -ε < f n ∧ f n < L + ε)

axiom r16: (0: ℝ) = 1

theorem singleton : x = 0 :=
begin
  rw [← r8 x, ← r16, r7]
end

#print axioms singleton
end ordring
