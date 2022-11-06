noncomputable theory

/- This one proves that a ring with axioms r1-r15,
   0 ≠ 1, and something between 0 and 1,
   is actually ℝ in disguise.

   This uses classical reasoning.
-/

open classical function -- lets us define functions by properties using "some"

local attribute [instance, priority 10] classical.prop_decidable
                        -- lets us use "if then else" with nondecidable properties
                        -- it implies excluded middle

constant real : Type
notation `ℝ` := real

namespace real

constant zero : real

constant one : real

constant add (x y: real) : real

constant mul (x y: real) : real

constant neg (x: real) : real

constant lt (x y: real) : Prop

instance : has_zero ℝ := ⟨zero⟩
instance : has_one ℝ := ⟨one⟩
instance : has_add ℝ := ⟨add⟩
instance : has_neg ℝ := ⟨neg⟩
instance : has_mul ℝ := ⟨mul⟩
instance : has_lt ℝ := ⟨lt⟩

variables (x y z t u: real)

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

axiom r16: ∃ (y: ℝ), 0 < y ∧ y < 1

theorem lt_irrefl : x < x → false := r1 x

theorem lt_trans : x < y → y < z → x < z := r2 x y z

theorem add_right_inj : x + y = x + z ↔ y = z :=
begin
  have l1: ∀ (x y z: ℝ), x = y → z + x = z + y,
  intros x y z h, rw [h],
  split ; intro h,
  have h2 := l1 _ _ (-x) h,
  rw [← r11, ← r11, r9 _ x, r14, r6, r6] at h2,
  assumption,
  apply l1, assumption,
end

theorem add_left_inj : y + x = z + x ↔ y = z :=
begin
  rw [r9 _ x, r9 _ x],
  apply add_right_inj,
end

theorem mul_pos : 0 < x → 0 < y → 0 < x * y := r5 x y

theorem mul_add : x * (y + z) = x * y + x * z :=  r13 x y z

theorem add_mul : (x + y) * z = x * z + y * z :=
begin
  rw [r10 _ z, r10 _ z, r10 _ z],
  apply r13
end

@[simp]
theorem neg_neg: (- (-x)) = x :=
begin
  rw [← add_right_inj, r14, r9, r14],
end

@[simp]
theorem neg_add: -(x + y) = (-x) + (-y) :=
begin
  rw [← add_right_inj (x + y), r14, r9 (-x), ← r11, r11 x, r14, r11, r6, r14],
end

@[simp]
theorem neg_mul:  -x * y = -(x * y) :=
begin
  rw [← add_right_inj, ← add_mul _ _ y, r14, r14, r7],
end

@[simp]
theorem mul_neg: x * (-y) = -(x * y) :=
begin
  rw [r10, neg_mul, r10]
end

@[simp]
theorem add_neg_self: x + (-x) = 0 := r14 x

@[simp]
theorem neg_add_self: (-x) + x = 0 :=
begin
  rw [r9, add_neg_self],
end

theorem zero_lt_one: (0: ℝ) < 1 :=
begin
  cases r16 with w h,
  cases h with h h',
  apply r2; assumption,
end

theorem add_comm : x + y = y + x := r9 x y

theorem add_assoc : x + y + z = x + (y + z) := r11 x y z

theorem mul_comm : x * y = y * x := r10 x y

theorem mul_assoc : x * y * z = x * (y * z) := r12 x y z

@[simp]
theorem zero_mul : 0 * x = 0 := r7 x

@[simp]
theorem mul_zero : x * 0 = 0 :=
begin
  rw [mul_comm, zero_mul],
end

@[simp]
theorem one_mul : 1 * x = x := r8 x

@[simp]
theorem mul_one : x * 1 = x :=
begin
  rw [mul_comm, one_mul],
end

@[simp]
theorem zero_add : 0 + x = x := r6 x

@[simp]
theorem add_zero : x + 0 = x :=
begin
  rw [add_comm, zero_add],
end

def sub (x y: real) : real := x + (-y)
instance : has_sub ℝ := ⟨sub⟩

@[simp]
private theorem add_simp_0 : x + (y + z) = x + y + z :=
  eq.symm (add_assoc x y z)

@[simp]
private theorem add_simp_1 : x + y + (-y) = x :=
begin
  rw [add_assoc, add_neg_self], simp
end

@[simp]
private theorem add_simp_2 : x + (-y) + y = x :=
begin
  rw [add_assoc, neg_add_self], simp
end

@[simp]
private theorem sub_simp_0 : x - y = x + (-y) := rfl

@[simp]
private theorem mul_simp_0 : x * (y * z) = x * y * z :=
  eq.symm (mul_assoc x y z)

@[simp]
theorem neg_zero : (-0) = (0: ℝ) :=
begin
  rw [← add_right_inj 0],
  rw [add_neg_self], simp
end

theorem add_switch : x + y + z = x + z + y :=
begin
  rw [add_assoc, add_comm y, ← add_assoc],
end

lemma lt_iff_zero_lt_sub : x < y ↔ 0 < y - x :=
begin
  split; intro h,
  have h2 := r4 _ _ (-x) h,
  simp at ⊢ h2, assumption,
  have h2 := r4 _ _ x h,
  simp at h2,
  assumption,
end

theorem neg_pos : 0 < -x ↔ x < 0 :=
begin
  split; intro h,
  have h1 := r4 _ _ x h,
  simp at h1, assumption,
  have h1 := r4 _ _ (-x) h,
  simp at h1, assumption,
end 

theorem neg_lt_zero : -x < 0 ↔ 0 < x :=
begin
  rw [← neg_pos, neg_neg],
end

theorem lt_trichotomy : x < y ∨ x = y ∨ y < x :=
begin
  cases r3 (y-x) with h,
  right, right,
  rw [lt_iff_zero_lt_sub, ← neg_lt_zero],
  simp at *,
  rw [add_comm], assumption,
  cases h with h h,
  right, left,
  rw [← add_right_inj (-x), add_comm _ x, add_comm _ y],
  simp at *, assumption,
  left, 
  rw [lt_iff_zero_lt_sub],
  assumption,
end

theorem add_lt_add_left : x + y < x + z ↔ y < z :=
begin
  split; intro h,
  have h1 := r4 _ _ (-x) h,
  rw [add_switch, add_neg_self, zero_add, add_switch, add_neg_self, zero_add ] at h1,
  assumption,
  rw [add_comm x, add_comm x], apply r4, assumption,
end

theorem add_lt_add_right : y + x < z + x ↔ y < z :=
begin
  rw [add_comm _ x, add_comm _ x],
  apply add_lt_add_left,
end

lemma mul_lt_mul_left (a0 : 0 < x) :  x * y < x * z ↔ y < z :=
begin
  have l : ∀ b c: ℝ, b < c → x * b < x * c,
  intros b c h,
  rw [lt_iff_zero_lt_sub] at h ⊢,
  simp at h ⊢,
  have h2 := mul_pos _ _ a0 h,
  rw [mul_add] at h2,
  simp at h2,
  exact h2,
  split; intro h,
  cases lt_trichotomy y z with h1 h1,
  assumption,
  cases h1 with h1 h1,
  exfalso, apply lt_irrefl (x * z), rw [h1] at h, assumption,
  have h2 := l z y h1,
  exfalso, apply lt_irrefl, apply lt_trans, exact h, assumption,
  apply l, assumption,
end

theorem mul_lt_mul_right (a0 : 0 < x): y * x < z * x ↔ y < z :=
begin
  rw [mul_comm _ x, mul_comm _ x],
  exact mul_lt_mul_left _ _ _ a0,
end

def le (x y: ℝ) : Prop := x < y ∨ x = y
instance : has_le ℝ := ⟨le⟩

private theorem le_def : x ≤ y ↔ x < y ∨ x = y :=
begin
  trivial
end

theorem le_refl : x ≤ x :=
begin
  rw [le_def], right, refl,  
end

theorem le_lt_trans : x ≤ y → y < z → x < z :=
begin
  intros h1 h2,
  rw [le_def] at h1, cases h1 with h1 h1,
  apply lt_trans; assumption,
  rw [h1], assumption,
end

theorem lt_le_trans : x < y → y ≤ z → x < z :=
begin
  intros h1 h2,
  rw [le_def] at h2, cases h2 with h2 h2,
  apply lt_trans; assumption,
  rw [← h2], assumption,
end

theorem le_of_lt : x < y → x ≤ y :=
begin
  intro,
  rw [le_def], left, assumption,
end

theorem le_antisymm : x ≤ y → y ≤ x → x = y :=
begin
  intros h1 h2,
  rw [le_def] at h1, cases h1 with h1 h1,
  exfalso, apply lt_irrefl, apply le_lt_trans; assumption,
  assumption,
end

theorem le_trans : x ≤ y → y ≤ z → x ≤ z :=
begin
  intros h1 h2,
  rw [le_def] at h1, cases h1 with h1 h1,
  apply le_of_lt, apply lt_le_trans; assumption,
  rw [h1], assumption
end

theorem mul_nonneg : 0 ≤ x → 0 ≤ y → 0 ≤ x * y :=
begin
  intros h1 h2,
  rw [le_def] at h1 h2,
  cases h1 with h1 h1; cases h2 with h2 h2,
  apply le_of_lt, apply mul_pos,
  assumption,
  assumption,
  simp [← h2], apply le_refl,
  simp [← h1], apply le_refl,
  simp [← h2], apply le_refl,
end

theorem le_lt_dichotomy : x < y ∨ y ≤ x :=
begin
  cases lt_trichotomy x y with h h,
  left, assumption,
  cases h with h h,
  right, rw [h], apply le_refl,
  right, apply le_of_lt, assumption,
end

theorem le_dichotomy : x ≤ y ∨ y ≤ x :=
begin
  cases le_lt_dichotomy x y with h h,
  left, apply le_of_lt, assumption,
  right, assumption,
end

lemma le_iff_zero_le_sub : x ≤ y ↔ 0 ≤ y - x :=
begin
  rw [le_def, le_def], split; intro h,
  cases h with h h,
  left, rw [← lt_iff_zero_lt_sub], assumption,
  right, rw [h], simp,
  cases h with h h,
  left, rw [lt_iff_zero_lt_sub], assumption,
  right,
  rw [← add_left_inj (-x)], simp at *, assumption,
end

theorem add_le_add_left : x + y ≤ x + z ↔ y ≤ z :=
begin
  rw [le_iff_zero_le_sub, le_iff_zero_le_sub y],
  simp, rw [add_switch x, add_neg_self, zero_add], 
end

theorem add_le_add_right : y + x ≤ z + x ↔ y ≤ z :=
begin
  rw [add_comm _ x, add_comm _ x],
  apply add_le_add_left,
end

theorem neg_nonneg : 0 ≤ -x ↔ x ≤ 0 :=
begin
  rw [le_iff_zero_le_sub, le_iff_zero_le_sub x],
  simp,
end 

theorem neg_le_zero : -x ≤ 0 ↔ 0 ≤ x :=
begin
  rw [le_iff_zero_le_sub, le_iff_zero_le_sub 0],
  simp,
end 

lemma mul_le_left (a0: 0 ≤ x) : y ≤ z → x * y ≤ x * z :=
begin
  rw [le_iff_zero_le_sub, le_iff_zero_le_sub (x * y)],
  simp,
  rw [← mul_neg, ← mul_add],
  intro,
  apply mul_nonneg, assumption, assumption,
end

lemma mul_le_right (a0 : 0 ≤ x) : y ≤ z → y * x ≤ z * x :=
begin
  rw [mul_comm _ x, mul_comm _ x],
  apply mul_le_left,
  assumption,
end

lemma mul_le_mul_left (a0 : 0 < x) :  x * y ≤ x * z ↔ y ≤ z :=
begin
  split; intro h,
  cases lt_trichotomy y z with h1 h1,
  apply le_of_lt, assumption,
  cases h1 with h1 h1,
  rw [h1], apply le_refl,
  exfalso, rw [← mul_lt_mul_left x] at h1,
  have h2 := lt_le_trans _ _ _ h1 h,
  apply lt_irrefl, exact h2,
  assumption,
  apply mul_le_left, apply le_of_lt, assumption,
  assumption,
end

theorem mul_le_mul_right (a0 : 0 < x): y * x ≤ z * x ↔ y ≤ z :=
begin
  rw [mul_comm _ x, mul_comm _ x],
  exact mul_le_mul_left _ _ _ a0,
end

theorem neg_lt_neg_iff : -x < -y ↔ y < x :=
begin
  rw [lt_iff_zero_lt_sub, lt_iff_zero_lt_sub y],
  simp,
  rw [add_comm _ x],
end

theorem neg_le_neg_iff : -x ≤ -y ↔ y ≤ x :=
begin
  rw [le_iff_zero_le_sub, le_iff_zero_le_sub y],
  simp,
  rw [add_comm _ x],
end

theorem zero_product : x * y = 0 → x = 0 ∨ y = 0 :=
begin
  intros xy,
  cases lt_trichotomy 0 x with hx hx; cases lt_trichotomy 0 y with hy hy,
  exfalso,
  have h1 := mul_pos _ _ hx hy,
  rw [xy] at h1,
  exact lt_irrefl _ h1,
  cases hy with hy hy,
  right, rw [hy],
  rw [← neg_lt_neg_iff] at hy, simp at hy,
  have h1 := mul_pos _ _ hx hy,
  simp at h1, rw [← neg_lt_neg_iff] at h1, simp at h1, rw [xy] at h1,
  exfalso, exact lt_irrefl _ h1,
  cases hx with hx hx,
  left, rw [hx],
  rw [← neg_lt_neg_iff] at hx, simp at hx,
  have h1 := mul_pos _ _ hx hy,
  simp at h1, rw [← neg_lt_neg_iff] at h1, simp at h1, rw [xy] at h1,
  exfalso, exact lt_irrefl _ h1,
  cases hx with hx hx; cases hy with hy hy,
  left, rw [hx],
  left, rw [hx],
  right, rw [hy],
  rw [← neg_lt_neg_iff] at hx, simp at hx,
  rw [← neg_lt_neg_iff] at hy, simp at hy,
  have h1 := mul_pos _ _ hx hy,
  simp at h1, rw [xy] at h1,
  exfalso, exact lt_irrefl _ h1,
end

theorem lt_add_lt : x < y → z < t → x + z < y + t :=
begin
  intros hxy hzt,
  apply lt_trans _ (y + z),
  rw [add_lt_add_right], assumption,
  rw [add_lt_add_left], assumption,
end

theorem lt_add_le : x < y → z ≤ t → x + z < y + t :=
begin
  intros hxy hzt,
  apply lt_le_trans _ (y + z),
  rw [add_lt_add_right], assumption,
  rw [add_le_add_left], assumption,
end

theorem le_add_lt : x ≤ y → z < t → x + z < y + t :=
begin
  intros hxy hzt,
  have l := lt_add_le _ _ _ _ hzt hxy,
  rw [add_comm x, add_comm y],
  assumption,
end

theorem le_add_le : x ≤ y → z ≤ t → x + z ≤ y + t :=
begin
  intros hxy hzt,
  apply le_trans _ (y + z),
  rw [add_le_add_right], assumption,
  rw [add_le_add_left], assumption,
end

theorem lt_iff_not_le : x < y ↔ ¬(y ≤ x) :=
begin
  split; intro h,
  intro h1,
  apply lt_irrefl, apply lt_le_trans; assumption,
  cases le_lt_dichotomy x y with h1 h1,
  assumption,
  exfalso, apply h, assumption,
end

theorem le_iff_not_lt : x ≤ y ↔ ¬(y < x) :=
begin
  split; intro h,
  intro h1, apply lt_irrefl, apply le_lt_trans; assumption,
  cases le_lt_dichotomy y x with h1 h1,
  exfalso, apply h, assumption,
  assumption,
end

theorem lt_self_add_one : x < x + 1 :=
begin
  rw [← add_lt_add_left (-x)], simp,
  apply zero_lt_one,
end

theorem add_nonneg : 0 ≤ x → 0 ≤ y → 0 ≤ x + y :=
begin
  intros hx hy,
  apply le_trans _ x,
  assumption,
  rw [le_iff_zero_le_sub], simp, rw [add_switch], simp, assumption,
end

theorem lt_mul_lt : 0 ≤ x → x < y → 0 ≤ z → z < t → x * z < y * t :=
begin
  intros x0 xy z0 zt,
  rw [lt_iff_zero_lt_sub] at xy zt ⊢,
  have h := mul_pos _ _ xy zt,
  simp at h ⊢,
  rw [mul_add, add_mul, add_mul] at h,
  simp at h,
  apply lt_le_trans,
  exact h,
  rw [le_iff_zero_le_sub],
  simp, rw [add_switch (y * t), add_neg_self, zero_add],
  have h1 :  -(x * z) + x * t + y * z + -(x * z) = x * (t - z) + (y - x) * z,
  simp, rw [mul_add, add_mul], simp,
  rw [add_comm (x * t)],
  rw [h1], apply add_nonneg,
  apply mul_nonneg, assumption, apply le_of_lt, assumption,
  apply mul_nonneg, apply le_of_lt, assumption, assumption,
end

noncomputable def npow : ℕ → ℝ → ℝ
| 0 x := one
| (nat.succ n) x := x * npow n x

instance : has_pow ℝ ℕ := {pow := λ x n, npow n x}

private lemma npow_succ : ∀ n: ℕ, npow (nat.succ n) x = x * npow n x :=
begin
  intro, unfold npow,
end

@[simp]
theorem pow_zero : x ^ 0 = 1 := begin refl, end

theorem pow_succ : ∀ n: ℕ, x ^ n.succ = x * (x ^ n) :=
begin
  intro, apply npow_succ,
end

@[simp]
theorem pow_one : x ^ 1 = x :=
begin
  rw [pow_succ], simp,
end

theorem pow_add : ∀ (m n: ℕ), x ^ (m + n) = x ^ m * x ^ n :=
begin
  intros m n,
  induction n with n hn,
  rw [nat.add_zero], simp,
  rw [nat.add_succ, pow_succ, hn, mul_comm, pow_succ, mul_assoc, mul_comm x],
end

theorem zero_pow : ∀ m: ℕ, 1 ≤ m → (0: ℝ) ^ m = 0 :=
begin
  intros m,
  induction m with m hm,
  intros hm0, exfalso, apply nat.le_lt_antisymm,
  exact hm0, apply nat.lt_succ_self,
  intro,
  rw [pow_succ, zero_mul],
end

theorem incb_seq : ∀ (f: ℕ → ℝ), (∀ (n: ℕ), f n < f (n + 1)) → (∃ (A: ℝ), ∀ (n: ℕ), f n ≤ A) → (∃ (L: ℝ), ∀ (ε: ℝ), 0 < ε → ∃ (N: ℕ), ∀ n, N ≤ n → L + -ε < f n ∧ f n < L + ε) :=
begin
  intros f hf hA,
  cases hA with A hA,
  have hA' : ∃ (B: ℝ), ∀ (n: ℕ), f n < B,
  existsi (A+1),
  intros n,
  apply le_lt_trans,
  exact hA n,
  have hA'' : A = A + 0,
  rw [add_zero],
  rw [hA'', add_assoc, zero_add, add_lt_add_left],
  apply zero_lt_one,
  have r := r15 f hf hA',
  cases r with L hr,
  existsi L,
  intros ε he,
  have hr1 := hr ε he,
  cases hr1 with N hN,
  existsi (N+1),
  intros n hn,
  apply hN,
  apply nat.lt_of_succ_le,
  exact hn,
end

theorem decb_seq : ∀ (f: ℕ → ℝ), (∀ (n: ℕ), f (n + 1) < f n) → (∃ (A: ℝ), ∀ (n: ℕ), A ≤ f n) → (∃ (L: ℝ), ∀ (ε: ℝ), 0 < ε → ∃ (N: ℕ), ∀ n, N ≤ n → L + -ε < f n ∧ f n < L + ε) :=
begin
  intros f hf hA,
  let g := λ n: ℕ, -(f n),
  have hg0 : ∀ (n: ℕ), g n = -(f n),
  intros n, refl,
  have hg : ∀ (n: ℕ), g n < g (n + 1),
  intros n, rw [hg0, hg0, neg_lt_neg_iff], apply hf,
  have hB : ∃ (B: ℝ), ∀ (n: ℕ), g n ≤ B,
  cases hA with A hA,
  existsi (-A),
  intros n,
  rw [hg0, neg_le_neg_iff], apply hA,
  have is := incb_seq g hg hB,
  cases is with L hL,
  existsi (-L),
  intros ε he,
  have hL2 := hL ε he,
  cases hL2 with N hL2,
  existsi N,
  intros n hn,
  have hL3 := hL2 n hn,
  cases hL3 with hL3 hL4,
  split,
  rw [hg0, ← neg_lt_neg_iff] at hL4, simp at hL4, assumption,
  rw [hg0, ← neg_lt_neg_iff] at hL3, simp at hL3, assumption,
end

private lemma pow_betw_zero_one_prop1 : 0 < x → x < 1 → ∀ n: ℕ, 0 < x ^ n  :=
begin
  intros h0 h1 n,
  induction n,
  rw [pow_zero], apply zero_lt_one,
  rw [pow_succ], apply r5; assumption,
end

private lemma pow_betw_zero_one_prop2 : 0 < x → x < 1 → ∀ n: ℕ, x ^ (n+1) < x ^ n :=
begin
  intros h0 h1 n,
  induction n with n hn,
  rw [nat.zero_add], simp, assumption,
  rw [pow_add, pow_succ, pow_succ], simp,
  rw [pow_succ] at hn,
  rw [mul_assoc, mul_lt_mul_left, mul_comm], assumption,
  assumption,
end

private lemma pow_betw_zero_one_prop3 : 0 < x → x < 1 → ∀ ε > 0, ∃ N: ℕ, ∀ n ≥ N, x ^ n < ε :=
begin
  intros h0 h1,
  let f := λ (n: ℕ), x ^ n,
  have hfn : ∀ (n: ℕ), f n = x ^ n,
  intros n, refl,
  have hd := decb_seq f (pow_betw_zero_one_prop2 x h0 h1),
  have hp : ∃ (A: ℝ), ∀ (n: ℕ), A ≤ f n,
  existsi (0: ℝ),
  intros n, apply le_of_lt, apply pow_betw_zero_one_prop1,
  assumption, assumption,
  have hp2 := hd hp,
  cases hp2 with L hL,
  clear hd hp,
  have hL0 : L = 0,
  cases lt_trichotomy 0 L with ht ht,
  let e1 := (1-x)*(1-x)*L,
  have he1 : e1 = (1-x)*(1-x)*L,
  refl,
  have : e1 > 0,
  apply mul_pos,
  apply mul_pos,
  rw [← lt_iff_zero_lt_sub], assumption,
  rw [← lt_iff_zero_lt_sub], assumption,
  assumption,
  have hL1 := hL e1 this,
  cases hL1 with N hN,
  have hN1 := (hN (N+1) _).left,
  have hN2 := (hN N _).right,
  rw [← mul_lt_mul_left x _ _ h0, hfn] at hN2,
  rw [hfn, pow_add, mul_comm] at hN1, simp at hN1,
  have hN3 := lt_trans _ _ _ hN1 hN2,
  rw [lt_iff_zero_lt_sub, he1] at hN3,
  simp [mul_add, add_mul] at hN3,
  rw [add_switch _ _ (x * x * L), add_comm] at hN3, simp at hN3,
  rw [add_switch _ _ (x * x * L), add_comm] at hN3, simp at hN3,
  rw [add_comm] at hN3, simp at hN3,
  rw [← neg_lt_zero] at hN3, simp at hN3,
  rw [← one_mul (x * x * L), mul_assoc (x * x), mul_assoc _ _ (x * L), ← mul_assoc x x L, ← neg_mul,
  ← add_mul, ← sub_simp_0] at hN3,
  have hN4 : (1 - x) * (x * x * L) > 0,
  apply mul_pos, rw [← lt_iff_zero_lt_sub], assumption,
  apply mul_pos, apply mul_pos, assumption, assumption, assumption,
  exfalso, apply lt_irrefl, apply lt_trans, exact hN3, exact hN4,
  apply nat.le_refl,
  apply nat.le_succ,
  cases ht with ht ht,
  rw [ht],
  let e1 := (-L),
  have he1 : e1 = (-L),
  refl,
  have : 0 < e1,
  rw [he1, neg_pos], assumption,
  have hL1 := hL e1 this,
  cases hL1 with N hN,
  have hN1 := (hN N _).right,
  simp [hfn] at hN1,
  have hN2 := pow_betw_zero_one_prop1 x h0 h1 N,
  exfalso, apply lt_irrefl, apply lt_trans, exact hN1, exact hN2,
  apply nat.le_refl,
  intros e he,
  have hL1 := hL e he,
  cases hL1 with N hN,
  existsi N,
  intros n hn,
  have hL2 := (hN n hn).right,
  rw [hL0, zero_add, hfn] at hL2,
  assumption,
end

private lemma ndb_seq_helper0 : x < y → z ≤ t → z - y < t - x :=
begin
  intros hxy hzt,
  rw [le_def] at hzt,
  cases hzt with h h,
  apply lt_trans _ (z-x),
  simp, rw [add_lt_add_left, neg_lt_neg_iff], assumption,
  simp, rw [add_lt_add_right], assumption,
  simp, rw [h, add_lt_add_left, neg_lt_neg_iff], assumption,
end

theorem ndb_seq: ∀ (f: ℕ → ℝ), (∀ (n: ℕ), f n ≤ f (n + 1)) → (∃ (A: ℝ), ∀ (n: ℕ), f n ≤ A) → (∃ (L: ℝ), ∀ (ε: ℝ), 0 < ε → ∃ (N: ℕ), ∀ n, N ≤ n → L + -ε < f n ∧ f n < L + ε) :=
begin
  intros f hfn hA,
  cases hA with A hA,
  cases r16 with q hq,
  cases hq with hq0 hq1,
  have hq2 : 0 < 1 - q,
  rw [← lt_iff_zero_lt_sub], assumption,
  let g := λ (n: ℕ), f n - q ^ n,
  have hg0 : ∀ n: ℕ, g n = f n - q ^ n,
  intros n, refl,
  have hgn : ∀ n: ℕ, g n < g (n+1),
  intros n,
  rw [hg0, hg0], apply ndb_seq_helper0,
  apply pow_betw_zero_one_prop2 q hq0 hq1,
  apply hfn,
  have hgA : ∃ B: ℝ, ∀ n: ℕ, g n ≤ B,
  existsi A,
  intros n, apply le_of_lt, apply lt_le_trans _ (f n),
  simp [hg0, lt_iff_zero_lt_sub], simp,
  apply pow_betw_zero_one_prop1 q hq0 hq1,
  apply hA,
  have hg := incb_seq g hgn hgA,
  cases hg with L hL,
  have hL' := pow_betw_zero_one_prop3 q hq0 hq1,
  existsi L, intros ε he,
  have hL1 := hL (q * ε) _,
  have hL2 := hL' ((1-q) * ε) _,
  cases hL1 with N1 hL1,
  cases hL2 with N2 hL2,
  existsi (max N1 N2), intros n hn,
  have hL3 := hL1 n _,
  cases hL3 with hL3 hL4,
  have hL5 : -((1-q)*ε) < q ^ n,
  apply lt_trans _ 0, rw [neg_lt_zero], apply mul_pos, assumption, assumption,
  apply pow_betw_zero_one_prop1, assumption, assumption,
  have hL6 := hL2 n _,
  have hfg : f n = g n + q ^ n,
  simp [hg0],
  rw [hfg], split,
  have hL35 := lt_add_lt _ _ _ _ hL3 hL5,
  simp [add_mul] at hL35, rw [add_switch] at hL35, simp at hL35, assumption,
  have hL46 := lt_add_lt _ _ _ _ hL4 hL6,
  simp [add_mul] at hL46, rw [add_switch] at hL46, simp at hL46, assumption, 
  apply @nat.le_trans _ (max N1 N2),
  apply le_max_right, assumption,
  apply @nat.le_trans _ (max N1 N2),
  apply le_max_left, assumption,
  apply mul_pos, assumption, assumption,
  apply mul_pos, assumption, assumption,
end

theorem nib_seq: ∀ (f: ℕ → ℝ), (∀ (n: ℕ), f (n + 1) ≤ f n) → (∃ (A: ℝ), ∀ (n: ℕ), A ≤ f n) → (∃ (L: ℝ), ∀ (ε: ℝ), 0 < ε → ∃ (N: ℕ), ∀ n, N ≤ n → L + -ε < f n ∧ f n < L + ε) :=
begin
  intros f hf hA,
  let g := λ n: ℕ, -(f n),
  have hg0 : ∀ (n: ℕ), g n = -(f n),
  intros n, refl,
  have hg : ∀ (n: ℕ), g n ≤ g (n + 1),
  intros n, rw [hg0, hg0, neg_le_neg_iff], apply hf,
  have hB : ∃ (B: ℝ), ∀ (n: ℕ), g n ≤ B,
  cases hA with A hA,
  existsi (-A),
  intros n,
  rw [hg0, neg_le_neg_iff], apply hA,
  have is := ndb_seq g hg hB,
  cases is with L hL,
  existsi (-L),
  intros ε he,
  have hL2 := hL ε he,
  cases hL2 with N hL2,
  existsi N,
  intros n hn,
  have hL3 := hL2 n hn,
  cases hL3 with hL3 hL4,
  split,
  rw [hg0, ← neg_lt_neg_iff] at hL4, simp at hL4, assumption,
  rw [hg0, ← neg_lt_neg_iff] at hL3, simp at hL3, assumption,
end

--floor function in a classical context
noncomputable def nat_cast : ℕ → ℝ
| (0: ℕ) := (0: ℝ)
| (nat.succ n) := 1 + nat_cast n

def int_cast : ℤ → ℝ
| (int.of_nat n) := nat_cast n
| -[1+(n: ℕ)] := -(1: ℝ) - (nat_cast n)

theorem int_cast_of_nat (n: ℕ) : int_cast (int.of_nat n) = nat_cast n := by refl

theorem nat_cast_respects_zero : nat_cast 0 = 0 :=
begin
  refl
end

theorem nat_cast_respects_one : nat_cast 1 = 1 :=
begin
  simp [nat_cast],
end

theorem nat_cast_respects_add (m n: ℕ) : nat_cast (m + n) = (nat_cast m) + (nat_cast n) :=
begin
  induction m with m hm,
  rw [nat.zero_add, nat_cast_respects_zero, zero_add],
  rw [nat.succ_add], simp [nat_cast], rw [hm, add_assoc], 
end

theorem nat_cast_respects_succ (m: ℕ) : nat_cast (m.succ) = nat_cast m + 1 :=
begin
  rw [add_comm], simp [nat_cast],
end

theorem nat_cast_respects_mul (m n: ℕ) : nat_cast (m * n) = (nat_cast m) * (nat_cast n) :=
begin
  induction m with m hm,
  rw [nat.zero_mul, nat_cast_respects_zero, zero_mul],
  rw [nat.succ_eq_add_one, nat.right_distrib, nat.one_mul, nat_cast_respects_add, hm,
  nat_cast_respects_add, add_mul, nat_cast_respects_one, one_mul],
end

private theorem nat_cast_nonneg (m: ℕ) : 0 ≤ nat_cast m :=
begin
  induction m with m hm,
  rw [nat_cast_respects_zero], apply le_refl,
  rw [nat_cast_respects_succ], apply le_trans _ (nat_cast m + 0),
  rw [add_zero], assumption,
  rw [add_le_add_left], apply le_of_lt, apply zero_lt_one,
end

private lemma nat_cast_respects_le_pre1 (m n: ℕ) : m ≤ n → nat_cast m ≤ nat_cast n :=
begin
  intros hmn,
  have h' := nat.add_sub_of_le hmn,
  rw [← h', nat_cast_respects_add, ← add_zero (nat_cast m), add_assoc, zero_add,
  add_le_add_left], apply nat_cast_nonneg
end

private lemma nat_cast_respects_le_pre2 (m n: ℕ) : m < n → nat_cast m < nat_cast n :=
begin
  intros hmn,
  have hmn' := nat_cast_respects_le_pre1 _ _ hmn,
  rw [nat_cast_respects_succ] at hmn',
  apply lt_le_trans _ (nat_cast m + 1),
  rw [← add_zero (nat_cast m), add_assoc, zero_add, add_lt_add_left], apply zero_lt_one,
  assumption,
end

theorem nat_cast_respects_le (m n: ℕ) : m ≤ n ↔ nat_cast m ≤ nat_cast n :=
begin
  split,
  apply nat_cast_respects_le_pre1,
  intro hmn,
  cases (nat.lt_or_ge n m),
  exfalso, apply lt_irrefl, apply le_lt_trans, assumption,
  apply nat_cast_respects_le_pre2, assumption,
  assumption,
end

theorem nat_cast_respects_lt (m n: ℕ) : m < n ↔ nat_cast m < nat_cast n :=
begin
  split,
  apply nat_cast_respects_le_pre2,
  intro hmn,
  cases (nat.lt_or_ge m n),
  assumption,
  exfalso, apply lt_irrefl, apply lt_le_trans, assumption,
  apply nat_cast_respects_le_pre1, assumption, 
end

theorem nat_cast_respects_eq (m n: ℕ) : m = n ↔ nat_cast m = nat_cast n :=
begin
  split,
  intro hmn, rw [hmn],
  intro hmn,
  apply nat.le_antisymm; rw [nat_cast_respects_le]; rw [hmn]; apply le_refl,
end

theorem int_cast_respects_zero : int_cast 0 = 0 :=
begin
  refl,
end

theorem int_cast_respects_one: int_cast 1 = 1 :=
begin
  have : 1 = int.of_nat 1,
  refl,
  rw [this],
  simp [int_cast],
  apply nat_cast_respects_one,
end

private lemma int_cast_respects_add_pre (a b: ℕ) : int_cast (int.sub_nat_nat a b) = nat_cast a - nat_cast b :=
begin
  apply int.sub_nat_nat_elim a b (λ x y z, int_cast z = nat_cast x - nat_cast y),
  intros i n,
  simp [int_cast], rw [nat_cast_respects_add, add_switch], simp,
  intros i m,
  simp [int_cast], rw [nat_cast_respects_add, nat_cast_respects_add,
  nat_cast_respects_one],
  simp, rw [add_comm],
end

theorem int_cast_respects_add (m n: ℤ) : int_cast (m + n) = (int_cast m) + (int_cast n) := 
begin
  cases m with a a; cases n with b b,
  rw [int.of_nat_add_of_nat], simp [int_cast], apply nat_cast_respects_add,
  rw [int.of_nat_add_neg_succ_of_nat, int_cast_respects_add_pre],
  simp [int_cast], simp [nat_cast],
  rw [int.neg_succ_of_nat_add_of_nat, int_cast_respects_add_pre],
  simp [int_cast], simp [nat_cast], rw [add_comm _ (nat_cast b), add_assoc],
  rw [int.neg_succ_of_nat_add_neg_succ_of_nat], simp [int_cast, nat_cast],
  rw [nat_cast_respects_add], simp, rw [add_switch (-1) (-1)],
end

theorem int_cast_respects_neg (m: ℤ) : int_cast (-m) = -(int_cast m) :=
begin
  rw [← add_right_inj (int_cast m), ← int_cast_respects_add, int.add_right_neg, add_neg_self],
  rw [int_cast_respects_zero],
end

theorem int_cast_respects_sub (m n: ℤ) : int_cast (m - n) = int_cast m - int_cast n :=
begin
  rw [int.sub_eq_add_neg, int_cast_respects_add, int_cast_respects_neg],
  simp,
end

private theorem int_cast_respects_le_pre1 (m n: ℤ) : m ≤ n → int_cast m ≤ int_cast n :=
begin
  intros h1,
  have h2 := int.add_le_add_right h1 (-m),
  rw [int.add_right_neg] at h2,
  have h3 := int.of_nat_nat_abs_eq_of_nonneg h2,
  have h4 : int_cast (int.of_nat (n + -m).nat_abs) = int_cast (n + -m),
  rw [h3],
  rw [int_cast_of_nat] at h4,
  have h5 : 0 ≤ int_cast (n + -m),
  rw [← h4], apply nat_cast_nonneg,
  rw [int_cast_respects_add, int_cast_respects_neg, ← sub_simp_0, ← le_iff_zero_le_sub] at h5,
  assumption,
end

private theorem int_cast_respects_le_pre2 (m n: ℤ) : m < n → int_cast m < int_cast n :=
begin
  intros h1,
  have h2 := int_cast_respects_le_pre1 _ _ h1,
  rw [int_cast_respects_add, int_cast_respects_one] at h2,
  apply lt_le_trans _ (int_cast m + 1),
  rw [← add_zero (int_cast m), add_assoc, zero_add, add_lt_add_left],
  apply zero_lt_one,
  assumption,  
end

theorem int_cast_respects_le (m n: ℤ) : m ≤ n ↔ int_cast m ≤ int_cast n :=
begin
  split; intro h,
  exact int_cast_respects_le_pre1 _ _ h,
  cases (le_or_lt m n) with h1 h1,
  assumption,
  have h2 := int_cast_respects_le_pre2 _ _ h1,
  exfalso, apply lt_irrefl, apply le_lt_trans; assumption,
end

theorem int_cast_respects_lt (m n: ℤ) : m < n ↔ int_cast m < int_cast n :=
begin
  split; intro h,
  exact int_cast_respects_le_pre2 _ _ h,
  cases (le_or_lt n m) with h1 h1,
  have h3 := int_cast_respects_le_pre1 _ _ h1,
  exfalso, apply lt_irrefl, apply le_lt_trans; assumption,
  assumption,
end

private lemma int_cast_respects_mul_pre (m: ℕ) (n: ℤ) : int_cast (int.of_nat m * n) = (int_cast (int.of_nat m)) * (int_cast n) :=
begin
  induction m with m hm,
  simp [int_cast, nat_cast],
  have : int.of_nat 0 = 0,
  refl,
  rw [this, int.zero_mul, int_cast_respects_zero],
  simp [int_cast, nat_cast],
  have rm : int.of_nat m.succ = int.of_nat m + 1,
  refl,
  rw [rm, int.distrib_right, int_cast_respects_add, hm], simp [int_cast],
  rw [int.one_mul, add_mul, one_mul], apply add_comm,
end

theorem int_cast_respects_mul (m n: ℤ) : int_cast (m * n) = (int_cast m) * (int_cast n) :=
begin
  cases m with b h,
  apply int_cast_respects_mul_pre,
  rw [← add_right_inj (int_cast ((1 +  int.of_nat h) * n))],
  rw [← int_cast_respects_add, int.distrib_right],
  rw [← int.distrib_right, ← int.distrib_right, int.neg_succ_of_nat_eq h],
  have l1 :  1 + int.of_nat h  = (↑h + 1),
  rw [int.add_comm], refl,
  have l2 : (↑h + 1) = int.of_nat (h + 1),
  rw [int.of_nat_add, int.of_nat_one], refl,
  rw [l1, int.add_right_neg, int.zero_mul, l2, int_cast_respects_mul_pre],
  rw [int_cast_respects_neg, ← add_mul, add_neg_self, int_cast_respects_zero, zero_mul],
end

private noncomputable def tec_f (x: ℝ) (hpx: 0 ≤ x) : ℕ → ℕ
| (0: ℕ) := (0: ℕ)
| (nat.succ n) := if (nat_cast (1 + tec_f n)) ≤ x then (1 + tec_f n) else (tec_f n)

private theorem tec_f_def0 (x: ℝ) (hpx: 0 ≤ x) : tec_f x hpx 0 = 0 :=
begin
  refl
end

private theorem tec_f_def1 (x: ℝ) (hpx: 0 ≤ x) : ∀ n: ℕ, tec_f x hpx (n+1) = if nat_cast (1 + tec_f x hpx n) ≤ x then (1 + tec_f x hpx n) else (tec_f x hpx n) :=
begin
  intro,
  simp [tec_f],
end

private theorem tec_f_def2 (x: ℝ) (hpx: 0 ≤ x) : ∀ (n: ℕ), nat_cast (1 + tec_f x hpx n) ≤ x → tec_f x hpx (n+1) = (1 + tec_f x hpx n) :=
begin
  intros n hn,
  simp [tec_f, hn],
end

private theorem tec_f_def3 (x: ℝ) (hpx: 0 ≤ x) : ∀ (n: ℕ), x < nat_cast (1 + tec_f x hpx n) → tec_f x hpx (n+1) = tec_f x hpx n :=
begin
  intros n hn,
  rw [lt_iff_not_le] at hn,
  simp [tec_f, hn],
end

private theorem tec_l1 (m n: ℕ) (q: ℝ): q < 1 → (nat_cast m) + (-q) < (nat_cast n) → (nat_cast n) < (nat_cast m) + q → m = n :=
begin
  have transl : ∀ m n:ℕ, m < n ↔ m.succ ≤ n,
  intros m n, refl,
  intros hq1 h1 h2,
  cases nat.lt_trichotomy m n with h,
  rw [transl, nat_cast_respects_le, nat_cast_respects_succ] at h,
  have h3 := le_add_lt _ _ _ _ h h2,
  rw [← add_assoc, add_assoc, add_comm 1, add_comm _ (nat_cast m), ← add_assoc] at h3,
  rw [add_lt_add_left] at h3,
  exfalso, apply lt_irrefl, apply lt_trans, exact hq1, exact h3,
  cases h with h h,
  assumption,
  rw [transl, nat_cast_respects_le, nat_cast_respects_succ] at h,
  have h3 := le_add_lt _ _ _ _ h h1,
  simp at h3, rw [add_switch (nat_cast n), add_comm (nat_cast n),
  ← add_zero (nat_cast m + nat_cast n), add_assoc (nat_cast m + nat_cast n),
  add_assoc (nat_cast m + nat_cast n), add_lt_add_left, zero_add] at h3,
  have h4 := lt_add_lt _ _ _ _ hq1 h3,
  rw [add_comm q] at h4, simp at h4,
  exfalso, apply lt_irrefl, assumption,
end

private theorem tec_f_nd (x: ℝ) (hpx: 0 ≤ x) : ∀ n: ℕ, tec_f x hpx n ≤ tec_f x hpx (n+1) :=
begin
  intro n,
  cases le_lt_dichotomy x (nat_cast (1 + tec_f x hpx n)) with h1 h1,
  rw [tec_f_def3],
  assumption,
  rw [tec_f_def2, ← nat.zero_add (tec_f x hpx n), ← nat.add_assoc, nat.add_zero],
  rw [nat.add_le_add_iff_right], apply nat.le_succ,
  assumption,
end

private theorem tec_f_b (x: ℝ) (hpx: 0 ≤ x) : ∀ n: ℕ, nat_cast (tec_f x hpx n) ≤ x :=
begin
  intro n,
  induction n with n hn,
  exact hpx,
  cases le_lt_dichotomy x (nat_cast (1 + tec_f x hpx n)) with h1 h1,
  rw [tec_f_def3], assumption, assumption,
  rw [tec_f_def2], assumption, assumption,
end

private theorem tec_floor1 (x: ℝ) (hpx: 0 ≤ x) : ∃ n: ℕ, nat_cast n ≤ x ∧ x < (nat_cast n) + 1 :=
begin
  have ex : ∃ A: ℝ, ∀ n: ℕ, nat_cast (tec_f x hpx n) ≤ A,
  existsi x, apply tec_f_b,
  have conv := ndb_seq
    (λ n, nat_cast (tec_f x hpx n))
    (λ n, (nat_cast_respects_le _ _).mp (tec_f_nd x hpx n))
    (ex),
  cases conv with L conv,
  simp at conv,
  cases r16 with q hq, cases hq with hq0 hq1,
  have hq2 : q * q + (1 - q) < 1,
  rw [lt_iff_zero_lt_sub], simp, rw [add_switch 1, add_neg_self, zero_add,
  ← neg_mul, ← one_mul q, ← mul_assoc, ← add_mul, mul_one, one_mul],
  apply mul_pos,
  rw [lt_iff_zero_lt_sub] at hq1, simp at hq1, rw [add_comm], assumption,
  assumption,
  have hq3 : 0 < q * q,
  apply mul_pos, assumption, assumption,
  have hq4 : 0 < 1 - q,
  rw [← lt_iff_zero_lt_sub], assumption,
  cases (conv (q * q) hq3) with N1 hN1,
  cases (conv (1-q) hq4) with N2 hN2,
  let N := (max N1 N2),
  have const : tec_f x hpx N = tec_f x hpx (N + 1),
  have hn1 := hN1 N _,
  cases hn1 with hn1 hn1b,
  have hn2 := hN2 (N+1) _,
  cases hn2 with hn2 hn2b,
  rw [← neg_lt_neg_iff] at hn1b,
  have hh := lt_add_lt _ _ _ _ hn1b hn2,
  simp at hh, rw [add_switch (-L), neg_add_self, zero_add] at hh,
  have : -(q * q) + -1 + q = -(q * q + (1 - q)),
  simp,
  rw [this] at hh,
  rw [← add_lt_add_left (nat_cast (tec_f x hpx N)), ← add_assoc,
  add_neg_self (nat_cast (tec_f x hpx N)), zero_add] at hh,
  rw [← neg_lt_neg_iff] at hn1,
  have hh' := lt_add_lt _ _ _ _ hn1 hn2b,
  simp at hh', rw [add_switch (-L), neg_add_self, zero_add] at hh',
  have : q * q + 1 + -q = q * q + (1 - q) := by simp,
  rw [this] at hh',
  rw [← add_lt_add_left (nat_cast (tec_f x hpx N)), ← add_assoc, add_neg_self, zero_add] at hh',
  apply tec_l1 _ _ _ hq2 hh hh',
  apply @nat.le_trans _ N,
  apply le_max_right,
  apply nat.le_succ_of_le,
  apply nat.le_refl,
  apply le_max_left,
  existsi (tec_f x hpx N),
  split,
  apply tec_f_b,
  cases le_lt_dichotomy x (nat_cast (1 + tec_f x hpx N)) with hc,
  rw [nat.add_comm, nat_cast_respects_add, nat_cast_respects_one] at hc,
  assumption,
  have h' := tec_f_def2 x hpx N h,
  rw [← const, ← nat.zero_add (tec_f x hpx N), ← nat.add_assoc, nat.add_zero] at h',
  have h'' := nat.add_right_cancel h',
  exfalso, apply (nat.succ_ne_self 0), apply eq.symm, assumption,
end

theorem exists_floor (x: ℝ) : ∃ k: ℤ, int_cast k ≤ x ∧ x < int_cast k + 1 :=
begin
  cases le_lt_dichotomy x 0 with hx,
  rw [← neg_lt_neg_iff, neg_zero] at hx,
  cases (tec_floor1 (-x) (le_of_lt _ _ hx)) with n hn,
  cases hn with hn1 hn2,
  cases le_lt_dichotomy (nat_cast n) (-x) with hxn,
  existsi (- int.of_nat n - 1),
  rw [int_cast_respects_sub, int_cast_respects_neg, int_cast_of_nat,
  int_cast_respects_one], simp,
  split,
  rw [← neg_le_neg_iff], simp, apply le_of_lt, assumption,
  rw [← neg_lt_neg_iff], simp, assumption,
  have hh := le_antisymm _ _ hn1 h,
  existsi (- int.of_nat n),
  rw [int_cast_respects_neg, int_cast_of_nat, hh, neg_neg],
  split,
  apply le_refl,
  apply lt_self_add_one,
  cases (tec_floor1 x h) with n hn,
  existsi (int.of_nat n),
  rw [int_cast_of_nat],
  assumption,
end

private theorem tec_floor1 (x: ℝ) (k m: ℤ) : int_cast k ≤ x → x < int_cast k + 1 → (int_cast m ≤ x ↔ m ≤ k) :=
begin
  intros ikx1 ikx2,
  split ; intro h,
  have h2 := le_lt_trans _ _ _ h ikx2,
  rw [← int_cast_respects_one, ← int_cast_respects_add, ← int_cast_respects_lt] at h2,
  have h3 := int.add_le_add_right h2 (-1:ℤ),
  rw [int.add_neg_cancel_right, int.add_neg_cancel_right] at h3,
  assumption,
  apply le_trans _ (int_cast k),
  rw [← int_cast_respects_le], assumption,
  assumption,
end

private theorem tec_floor2 (x: ℝ) (k m: ℤ) : int_cast k ≤ x → x < int_cast k + 1 → (x < int_cast m ↔ k + 1 ≤ m) :=
begin
  intros ikx1 ikx2,
  split ; intro h,
  cases (le_or_lt (k + 1) m) with hkm hkm,
  assumption,
  have hkm2 := int.add_le_add_right hkm (-1: ℤ),
  rw [int.add_neg_cancel_right, int.add_neg_cancel_right] at hkm2,
  have hkm3 := (tec_floor1 _ _ _ ikx1 ikx2).mpr hkm2,
  exfalso, apply lt_irrefl, apply lt_le_trans x (int_cast m); assumption,
  apply lt_le_trans,
  assumption,
  rw [← int_cast_respects_one, ← int_cast_respects_add, ← int_cast_respects_le],
  assumption,
end

noncomputable def floor (x: ℝ): ℤ := some (exists_floor x)

theorem floor_def (x: ℝ) : int_cast (floor x) ≤ x ∧ x < int_cast (floor x) + 1 :=
begin
  apply some_spec (exists_floor x),
end

theorem floor_unique (x: ℝ): ∀ (k: ℤ), int_cast k ≤ x → x < int_cast k + 1 → k = floor x :=
begin
  intros k hkx1 hkx2,
  cases floor_def x with hmx1 hmx2,
  have c1 := (tec_floor1 x k (floor x) hkx1 hkx2).mp hmx1,
  have c2 := (tec_floor1 x (floor x) k hmx1 hmx2).mp hkx1,
  apply int.le_antisymm ; assumption,
end

theorem int_le_floor (x: ℝ) : ∀ (m: ℤ), int_cast m ≤ x ↔ m ≤ floor x :=
begin
  cases floor_def x with hx1 hx2,
  intros m,
  apply (tec_floor1 x (floor x) m hx1 hx2),
end

theorem lt_int_floor (x: ℝ) : ∀ (m: ℤ), x < int_cast m ↔ floor x < m :=
begin
  cases floor_def x with hx1 hx2,
  intros m,
  apply (tec_floor2 x (floor x) m hx1 hx2),
end

-- multiplicative inverse in classical context
private theorem tec_bound (y: ℝ) : 0 < y → (∀ x: ℝ, x * y ≤ 1) → false :=
begin
  intros hy hx,
  let f := λ k: ℕ, (nat_cast k) * y,
  have f_inc : ∀ k: ℕ, f k ≤ f (k + 1),
  intros k, simp [f], rw [le_iff_zero_le_sub], simp,
  rw [← neg_mul, ← add_mul, nat_cast_respects_add, add_switch, add_neg_self, zero_add,
  nat_cast_respects_one, one_mul],
  apply le_of_lt, assumption,
  have f_bound : (∃ A: ℝ, ∀ k: ℕ, f k ≤ A),
  existsi (1: ℝ), 
  simp [f], intro k, apply hx,
  have f_tends := ndb_seq f f_inc f_bound,
  cases f_tends with L hL,
  cases (hL y hy) with N hN,
  have hN1 := (hN N _).left,
  have hN2 := (hN (N+1+1) _).right,
  simp [f] at hN1 hN2,
  rw [nat_cast_respects_add, add_mul, nat_cast_respects_add, add_mul,
  nat_cast_respects_one, one_mul] at hN2,
  rw [← add_lt_add_right y, add_switch, add_assoc, add_neg_self, add_zero,
  ← add_lt_add_right y] at hN1,
  apply lt_irrefl (L + y), apply lt_trans; assumption,
  apply nat.le_trans, apply nat.le_succ, apply nat.le_succ,
  apply nat.le_refl,
end

def tendsto_gs (a : ℕ → ℝ) (L : ℝ) := ∀ ε > 0, ∃ N: ℕ, ∀ n ≥ N, L + (-ε) < a n ∧ a n < L + ε

theorem sandwich_gs (a b c: ℕ → ℝ) (L: ℝ): (∀ n, a n ≤ b n) → (∀ n, b n ≤ c n) → tendsto_gs a L → tendsto_gs c L → tendsto_gs b L :=
begin
  intros hab hbc hta htc,
  intros ε hε,
  cases (hta ε hε) with N1 hN1,
  cases (htc ε hε) with N2 hN2,
  existsi (max N1 N2),
  intros n hn,
  split,
  apply lt_le_trans _ (a n),
  apply (hN1 n _).left,
  apply @nat.le_trans _ (max N1 N2),
  apply le_max_left, assumption,
  apply hab,
  apply le_lt_trans _ (c n),
  apply hbc,
  apply (hN2 n _).right,
  apply @nat.le_trans _ (max N1 N2),
  apply le_max_right, assumption,
end

theorem tendsto_add_gs (a b: ℕ → ℝ) (L M: ℝ): tendsto_gs a L → tendsto_gs b M → tendsto_gs (λ n, a n + b n) (L + M) :=
begin
  cases r16 with q hq, cases hq with hq1 hq2,
  intros ha hb,
  simp [tendsto_gs],
  intros ε hε,
  cases (ha (q * ε) _) with N1 hN1,
  cases (hb ((1-q) * ε) _) with N2 hN2,
  existsi (max N1 N2),
  intros n hn,
  have hN2' := hN2 n _,
  cases hN2' with hN21 hN22,
  have hN1' := hN1 n _,
  cases hN1' with hN11 hN12,
  split,
  have hh := lt_add_lt _ _ _ _ hN11 hN21,
  rw [add_switch] at hh, simp at hh,
  rw [← neg_mul, ← neg_mul, add_assoc, ← add_mul, neg_add, neg_neg,
  add_assoc (-1), add_neg_self, add_zero, neg_mul, one_mul] at hh,
  assumption,
  have hh := lt_add_lt _ _ _ _ hN12 hN22,
  rw [add_switch, ← add_assoc, add_assoc, ← add_mul] at hh,
  simp [sub] at hh, assumption,
  apply @nat.le_trans _ (max N1 N2),
  apply le_max_left, exact hn,
  apply @nat.le_trans _ (max N1 N2),
  apply le_max_right, exact hn,
  apply mul_pos,
  rw [← lt_iff_zero_lt_sub], assumption,
  assumption,
  apply mul_pos,
  assumption,
  assumption,
end

theorem tendsto_constant_gs (L: ℝ) : tendsto_gs (λ n, L) L :=
begin
  intros ε hε,
  existsi 0,
  intros n hn,
  simp,
  split ; rw [lt_iff_zero_lt_sub],
  simp, assumption,
  simp, rw [add_switch, add_neg_self, zero_add], 
  assumption,
end

theorem tendsto_neg_gs (a: ℕ → ℝ) (L: ℝ) : tendsto_gs a L → tendsto_gs (λ n, -(a n)) (-L) :=
begin
  intros h ε hε,
  cases (h ε hε) with N hN,
  existsi N,
  intros n hn,
  cases (hN n hn) with hN1 hN2,
  simp, split,
  rw [← neg_lt_neg_iff], simp, assumption,
  rw [← neg_lt_neg_iff], simp, assumption,
end

theorem tendsto_iff_tendsto_zero_gs (a: ℕ → ℝ) (L: ℝ) : tendsto_gs a L ↔ tendsto_gs (λ n, a n - L) 0 :=
begin
  simp, split; intro h,
  have h1 := tendsto_add_gs a (λ n, (-L)) L (-L) h (tendsto_constant_gs (-L)),
  simp at h1, assumption,
  have h1 := tendsto_add_gs _ (λ n, L) 0 L h (tendsto_constant_gs L),
  simp at h1, assumption,
end

/-private theorem tendsto_mul_zero_gs_pre1: ∀ (A B: ℝ), 0 < A → 0 < B → - A < x → x < A → -B < y → y < B → 0 ≤ x → 0 ≤ y → -(A * B) < x * y ∧ x * y < (A * B) :=
begin
  intros A B hA hB hx1 hx2 hy1 hy2 hx3 hy3,
  split,
  apply lt_le_trans _ 0,
  rw [lt_iff_zero_lt_sub], simp, apply mul_pos; assumption,
  apply mul_nonneg; assumption,
  apply lt_mul_lt; assumption,
end

private theorem tendsto_mul_zero_gs_pre2: ∀ (A B: ℝ), 0 < A → 0 < B → - A < x → x < A → -B < y → y < B → -(A * B) < x * y ∧ x * y < (A * B) :=
begin
  have n : ∀ z: ℝ, z ≤ 0 → 0 ≤ -z,
  intros z, intro h,
  rw [← neg_le_neg_iff], simp, assumption,
  intros A B hA hB hx1 hx2 hy1 hy2,
  have hx1' := hx1, rw [← neg_lt_neg_iff] at hx1', simp at hx1',
  have hx2' := hx2, rw [← neg_lt_neg_iff] at hx2',
  have hy1' := hy1, rw [← neg_lt_neg_iff] at hy1', simp at hy1',
  have hy2' := hy2, rw [← neg_lt_neg_iff] at hy2',
  cases le_dichotomy 0 x with hx hx; cases le_dichotomy 0 y with hy hy,
  apply (tendsto_mul_zero_gs_pre1 _ _ _ _ hA hB hx1 hx2 hy1 hy2 hx hy),
  have h1 := tendsto_mul_zero_gs_pre1 _ _ _ _ hA hB hx1 hx2 hy2' hy1' hx (n _ hy),
  cases h1 with h12 h13, rw [← neg_lt_neg_iff] at h12 h13, simp at h12 h13, split ; assumption,
  have h1 := tendsto_mul_zero_gs_pre1 _ _ _ _ hA hB hx2' hx1' hy1 hy2 (n _ hx) hy,
  cases h1 with h12 h13, rw [← neg_lt_neg_iff] at h12 h13, simp at h12 h13, split ; assumption,
  have h1 := tendsto_mul_zero_gs_pre1 _ _ _ _ hA hB hx2' hx1' hy2' hy1' (n _ hx) (n _ hy),
  cases h1 with h12 h13, simp at h12 h13, split ; assumption,
end

private theorem tendsto_mul_zero_gs (a b: ℕ → ℝ): tendsto_gs a 0 → tendsto_gs b 0 → tendsto_gs (λ n, a n * b n) 0 :=
begin
  intros ha hb ε hε,
  simp,
  cases (ha 1 zero_lt_one) with N1 hN1,
  cases (hb ε hε) with N2 hN2,
  simp at hN1 hN2,
  existsi (max N1 N2),
  intros n hn,
  have hN1' := hN1 n _,
  have hN2' := hN2 n _,
  have t := tendsto_mul_zero_gs_pre2 _ _ _ _ zero_lt_one hε (hN1'.left) (hN1'.right) (hN2'.left) (hN2'.right),
  rw [one_mul] at t, assumption,
  apply @nat.le_trans _ (max N1 N2),
  apply le_max_right, assumption,
  apply @nat.le_trans _ (max N1 N2),
  apply le_max_left, assumption,
end

theorem tendsto_mul_gs (a b: ℕ → ℝ) (L M: ℝ): tendsto_gs a L → tendsto_gs b M → tendsto_gs (λ n, a n * b n) (L * M) :=
begin
  intros ha hb,
  rw [tendsto_iff_tendsto_zero_gs] at ha hb ⊢,
  have h1 := tendsto_mul_zero_gs _ _ ha hb,
  simp at h1, simp [add_mul] at h1, simp [mul_add] at h1,
  
end
-/

private theorem tendsto_zero_geom_pre1 (x q: ℝ) : 0 < q → q < 1 → x < 0 → tendsto_gs (λ n, x * q ^ n) 0 :=
begin
  intros hqM hq0 hx0,
  have hx0' := hx0,
  rw [← neg_lt_neg_iff] at hx0', simp at hx0',
  let f := λ n: ℕ, x * q ^ n,
  have f_nd : ∀ n, f n ≤ f (n + 1),
  intro n,
  rw [← neg_le_neg_iff, ← neg_mul, ← neg_mul, mul_le_mul_left],
  apply le_of_lt, apply pow_betw_zero_one_prop2,
  assumption, assumption, assumption,
  have f_b1 : ∀ n, f n < 0,
  intro n,
  rw [← neg_lt_neg_iff, neg_zero, ← neg_mul],
  apply mul_pos,
  assumption,
  apply pow_betw_zero_one_prop1,
  assumption, assumption,
  have f_b : ∃ A, ∀ n, f n ≤ A,
  existsi (0: ℝ),
  intros n, apply le_of_lt, apply f_b1,
  cases (ndb_seq f f_nd f_b) with L hL,
  clear f_nd f_b,
  have L0 : L = 0,
  cases lt_trichotomy 0 L with h h,
  cases (hL L h) with N hN,
  have hN' := (hN N _).left,
  simp at hN',
  exfalso, apply lt_irrefl, apply lt_trans 0, exact hN', apply f_b1,
  apply nat.le_refl,
  cases h with h h,
  rw [h],
  cases (hL ((-L)*(1-q)*(1-q)) _) with N hN,
  have hN1 := (hN N _).left,
  have hN2 := (hN (N+1) _).right,
  simp [f] at hN2, rw [pow_succ q N, mul_comm q, ← mul_assoc] at hN2,
  rw [← mul_lt_mul_right q] at hN1, simp [f] at hN1,
  have hN' := lt_trans _ _ _ hN1 hN2,
  rw [lt_iff_zero_lt_sub] at hN',
  simp at hN', rw [← mul_neg, mul_add, mul_one, mul_add, neg_add, mul_add,
  add_mul, add_mul, mul_one, add_mul, add_mul, add_mul, add_mul, add_mul] at hN',
  simp at hN', rw [add_switch _ (-(L * q * q)), add_assoc _ (L * q),
  add_neg_self, add_zero, add_switch _ (-(L * q * q)), add_neg_self, zero_add] at hN',
  rw [add_comm (-(L * q * q)), add_neg_self, zero_add] at hN',
  have : L * q * q + -(L * q * q * q) = L * q * q * (1 - q),
  simp, rw [mul_add (L * q * q), mul_one], simp,
  rw [this, ← neg_lt_neg_iff, neg_zero, mul_assoc L, mul_assoc L, ← neg_mul L] at hN',
  exfalso, apply lt_irrefl 0, apply lt_trans _ (-L * (q * q * (1-q))),
  apply mul_pos,
  rw [← neg_lt_neg_iff, neg_neg, neg_zero], assumption,
  apply mul_pos, apply mul_pos ; assumption,
  rw [← lt_iff_zero_lt_sub], assumption,
  assumption,
  assumption,
  apply nat.le_succ,
  apply nat.le_refl,
  apply mul_pos,
  apply mul_pos,
  rw [← neg_lt_neg_iff, neg_neg, neg_zero], assumption,
  rw [← lt_iff_zero_lt_sub], assumption,
  rw [← lt_iff_zero_lt_sub], assumption,
  rw [L0] at hL,
  exact hL,
end

theorem geom_tendsto_zero (x q: ℝ) : -1 < q → q < 1 → tendsto_gs (λ n, x * q ^ n) 0 :=
begin
  intros hqm hqM,
  have case1 : ∀ (x q: ℝ), 0 < x → 0 < q → q < 1 → tendsto_gs (λ n, x * q ^ n) 0,
  intros x q hx hq hqM,
  have hx' := hx,
  rw [← neg_lt_neg_iff, neg_zero] at hx',
  have h1 := tendsto_neg_gs _ 0 (tendsto_zero_geom_pre1 _ _ hq hqM hx'), simp at h1,
  assumption,
  have case2 : ∀ (x q: ℝ), 0 < x → q < 0 → -1 < q → tendsto_gs (λ n, x * q ^ n) 0,
  intros x q hx hq hqm,
  have : ∀ n: ℕ, - ((-q) ^ n) ≤ q ^ n ∧ q ^ n ≤ (-q) ^ n,
  intro n,
  induction n with n hn,
  simp, split,
  apply le_trans _ 0,
  rw [le_iff_zero_le_sub], apply le_of_lt, simp, apply zero_lt_one,
  apply le_of_lt, apply zero_lt_one,
  apply le_refl,
  rw [pow_succ, pow_succ], simp,
  cases hn with hn1 hn2,
  have hn1' := mul_le_left (-q) _ _ _ hn1,
  have hn2' := mul_le_left (-q) _ _ _ hn2,
  rw [← neg_le_neg_iff] at hn1' hn2',
  simp at hn1' hn2',
  split; assumption,
  rw [← neg_le_neg_iff, neg_neg, neg_zero], apply le_of_lt, assumption,
  rw [← neg_le_neg_iff, neg_neg, neg_zero], apply le_of_lt, assumption,
  have t : ∀ (n: ℕ), -(x * (-q) ^ n) ≤ x * q ^ n ∧ x * q ^ n ≤ (x * (-q) ^ n),
  intros n,
  have t1 := (this n).left,
  have t2 := (this n).right,
  rw [← mul_le_mul_left _ _ _ hx] at t1 t2,
  simp at t1,
  split; assumption,
  let a := λ n: ℕ, -(x * (-q) ^ n),
  let b := λ n: ℕ, (x * (-q) ^ n),
  apply sandwich_gs a _ b,
  intros n, apply (t n).left,
  intros n, apply (t n).right,
  simp [a], rw [← neg_zero], apply tendsto_neg_gs, apply case1,
  assumption, rw [← neg_lt_neg_iff, neg_neg, neg_zero], assumption,
  rw [← neg_lt_neg_iff, neg_neg], assumption,
  simp [b], apply case1, assumption, rw [← neg_lt_neg_iff, neg_zero, neg_neg],
  assumption, rw [← neg_lt_neg_iff, neg_neg], assumption,
  have case3 : ∀ (x q: ℝ), 0 < x → -1 < q → q < 1 → tendsto_gs (λ n, x * q ^ n) 0,
  intros x q hx hqm hqM,
  cases lt_trichotomy 0 q with h h,
  apply case1; assumption,
  cases h with h h,
  intros ε hε, existsi 1, intros n hn, rw [← h], simp, rw [zero_pow, mul_zero],
  split,
  rw [← neg_lt_neg_iff, neg_neg, neg_zero], assumption, assumption, assumption,
  apply case2; assumption,
  clear case1 case2,
  have case4 : ∀ (x q: ℝ), x < 0 → -1 < q → q < 1 → tendsto_gs (λ n, x * q ^ n) 0,
  intros x q hx hqm hqM,
  have c := case3 (-x) q _ hqm hqM,
  have c' := tendsto_neg_gs _ _ c,
  simp at c', assumption,
  rw [← neg_lt_neg_iff, neg_neg, neg_zero], assumption,
  cases lt_trichotomy 0 x with h h,
  apply case3 x q h hqm hqM,
  cases h with h h,
  simp [← h, zero_mul], apply tendsto_constant_gs,
  apply case4 x q h hqm hqM,
end

theorem upper_geom (a: ℕ → ℝ) (q: ℝ): 
  0 ≤ q
  → (∀ n, a (n + 1) ≤ q * a n)
  → (∀ n, a n ≤ (a 0) * q ^ n) :=
begin
  intros hq hm n,
  induction n with n hr,
  simp, apply le_refl,
  apply le_trans, apply hm,
  rw [pow_succ, ← mul_assoc, mul_comm (a 0), mul_assoc],
  apply mul_le_left,
  assumption,
  assumption,
end

theorem tendsto_zero_upper_geom (a: ℕ → ℝ) (q: ℝ):
  0 ≤ q
  → q < 1
  → (∀ n, a (n + 1) ≤ q * a n)
  → (∀ n, 0 ≤ a n)
  → tendsto_gs a 0 :=
begin
  intros hq0 hq1 hM hm,
  have h1 := geom_tendsto_zero (a 0) q _ hq1,
  have h2 := upper_geom a q hq0 hM,
  apply sandwich_gs (λ n, 0) _ (λ n, (a 0) * q ^ n),
  simp, apply hm,
  simp, apply h2,
  apply tendsto_constant_gs,
  apply h1,
  apply lt_le_trans _ 0,
  rw [lt_iff_zero_lt_sub], simp, apply zero_lt_one,
  assumption,
end

private theorem nested_intervals_pre (a: ℕ → ℝ) (n0: ℕ):
  (∀ n, a (n + 1) ≤ a n) → (∀ n, a (n0 + n) ≤ a n0) :=
begin
  intros hni n,
  induction n with n hr,
  rw [nat.add_zero], apply le_refl,
  have hc := hni (n0 + n),
  rw [nat.add_assoc] at hc,
  apply le_trans; assumption,
end

theorem ni_conv_bound (a: ℕ → ℝ) (L: ℝ):
  (∀ n, a (n + 1) ≤ a n)
  → tendsto_gs a L
  → (∀ n, L ≤ a n) :=
begin
  intros hani hac n0,
  cases le_lt_dichotomy (a n0) L,
  have h1 := nested_intervals_pre a n0 hani,
  cases (hac (L + (-a n0)) _) with N h2,
  have h2' := (h2 (max N n0) _).left,
  simp at h2',
  have h3 : n0 ≤ (max N n0),
  apply le_max_right,
  cases (nat.le.dest h3) with k hk,
  exfalso, apply lt_irrefl, apply lt_le_trans (a n0),
  exact h2',
  rw [← hk], apply h1,
  apply le_max_left,
  rw [lt_iff_zero_lt_sub] at h,
  simp at h,
  assumption,
  assumption,
end

theorem nd_conv_bound (a: ℕ → ℝ) (L: ℝ):
  (∀ n, a n ≤ a (n + 1))
  → tendsto_gs a L
  → (∀ n, a n ≤ L) :=
begin
  intros hand hac,
  let b := λ n, -(a n),
  have hbc := tendsto_neg_gs a L hac,
  have hbni : ∀ n, b (n + 1) ≤ b n,
  intros n, simp [b], rw [neg_le_neg_iff], apply hand,
  have hb := ni_conv_bound b _ hbni hbc,
  intros n, rw [← neg_le_neg_iff], apply hb,
end

theorem nested_intervals (a b: ℕ → ℝ) :
  (∀ n, a n ≤ a (n + 1))
  → (∀ n, b (n + 1) ≤ b n)
  → tendsto_gs (λ n, b n - a n) 0
  → ∃ L: ℝ, tendsto_gs a L ∧ tendsto_gs b L ∧ (∀ n, a n ≤ L) ∧ (∀ n, L ≤ b n) :=
begin
  intros ha hb hab,
  let f := λ n, b n - a n,
  have fni : ∀ n, f (n + 1) ≤ f n,
  intros n, simp [f], apply le_add_le, apply hb, rw [← neg_le_neg_iff, neg_neg, neg_neg], apply ha,
  have hab' : tendsto_gs f 0,
  simp [f], simp [sub] at hab, assumption, 
  have hfb := ni_conv_bound f 0 fni hab',
  have habc : ∀ n, a n ≤ b n,
  intros n, rw [le_iff_zero_le_sub], apply hfb,
  have a_b: ∃ A, ∀ n, a n ≤ A,
  existsi (b 0),
  intros n, apply le_trans _ (b n),
  apply habc,
  have hh := nested_intervals_pre b 0 hb,
  simp [nat.zero_add] at hh, apply hh,
  cases (ndb_seq a ha a_b) with L hL,
  have hca : tendsto_gs a L,
  exact hL,
  have hcb : tendsto_gs b L,
  have hh := tendsto_add_gs a f L 0 hca hab',
  have hhn : ∀ n, a n + f n = b n,
  intros n, simp [f], rw [add_switch], simp,
  simp [hhn] at hh, assumption,
  existsi L, split,
  assumption,
  split, assumption,
  split,
  exact nd_conv_bound a L ha hca,
  exact ni_conv_bound b L hb hcb,
end

private noncomputable def nested_interval_search_pre (P: ℝ → Prop) (u v: ℝ) (huv : u < v) (q: ℝ): ℕ → ℝ × ℝ
| (0: ℕ) := ⟨u, v⟩
| (nat.succ n: ℕ) := 
let a := (nested_interval_search_pre n).fst in
let b := (nested_interval_search_pre n).snd in
let m := q * a + (1 - q) * b in
if P m then ⟨m, b⟩ else ⟨a, m⟩

theorem nested_interval_search (P: ℝ → Prop) (Pem: ∀ x, P x ∨ ¬(P x)) (u v: ℝ) (huv : u < v) (hu: P u) (hv: ¬(P v)) (q: ℝ) (hq: 0 < q ∧ q < 1 ∧ 1 - q ≤ q):
  ∃ (a b: ℕ → ℝ) (L: ℝ),
  a 0 = u
  ∧ b 0 = v
  ∧ (∀ n, a n ≤ a (n + 1))
  ∧ (∀ n, b (n + 1) ≤ b n)
  ∧ (∀ n, a n ≤ L)
  ∧ (∀ n, L ≤ b n)
  ∧ tendsto_gs a L
  ∧ tendsto_gs b L
  ∧ (∀ n, P (a n))
  ∧ (∀ n, ¬ (P (b n)))
  ∧ (∀ n, b (n + 1) - a (n + 1) ≤ q * (b n - a n)) :=
begin
  let ab := nested_interval_search_pre P u v huv q,
  have dab : ab = nested_interval_search_pre P u v huv q := by refl,
  let a := λ n, (ab n).1,
  let b := λ n, (ab n).2,
  have habn0 : ∀ n, ab n = ⟨a n, b n⟩,
  simp [a, b],
  have habn := λ n, eq.symm (habn0 n), clear habn0,
  have h0 : a 0 = u ∧ b 0 = v,
  apply prod.mk.inj, rw [habn], refl,
  cases h0 with ha0 hb0,
  existsi a, existsi b,
  have case0: ∀ n, let m := q * (a n) + (1 - q) * (b n) in
    ab (nat.succ n) = if (P m) then ⟨m, b n⟩ else ⟨a n, m⟩,
  intros n m, simp only [ab, nested_interval_search_pre],
  have case1: ∀ n, let m := q * (a n) + (1 - q) * (b n) in
    P m → a (n + 1) = m ∧ b (n + 1) = b n,
  intros n m hPm, have := case0 n,
  simp [m] at hPm,
  simp [hPm] at this,
  apply prod.mk.inj, simp [m], apply this,
  have case2: ∀ n, let m := q * (a n) + (1 - q) * (b n) in
    ¬(P m) → a (n + 1) = a n ∧ b (n + 1) = m,
  intros n m hPm, have := case0 n,
  simp [m] at hPm,
  simp [hPm] at this,
  apply prod.mk.inj, simp [m], apply this,
  clear case0 habn,
  have propab : ∀ n, a n ≤ b n → a n ≤ a (n + 1) ∧ a (n + 1) ≤ b (n + 1) ∧ b (n + 1) ≤ b n ∧ b (n + 1) - a (n + 1) ≤ q * (b n - a n),
  intros n habn,
  let m := q * (a n) + (1 - q) * (b n),
  cases hq with hq1 hq2,
  cases hq2 with hq2 hq3,
  have hdm : m = q * (a n) + (1 - q) * (b n),
  refl,
  cases (Pem m) with hmx hmx,
  have case1n := case1 n hmx,
  cases case1n with ha hb,
  split,
  rw [ha, le_iff_zero_le_sub],
  have : q * a n + (1 - q) * b n - a n = (1 - q) * (b n - a n),
  simp, rw [add_mul, add_mul, one_mul, one_mul, mul_add], simp,
  rw [add_comm (q * a n), add_switch _ _ (-a n), add_switch _ _ (-a n),
  add_switch _ _ (-(q * b n))],
  rw [this],
  apply mul_nonneg,
  rw [← le_iff_zero_le_sub], apply le_of_lt, assumption,
  rw [← le_iff_zero_le_sub], assumption,
  split,
  rw [ha, hb, le_iff_zero_le_sub],
  have : b n - (q * a n + (1 - q) * b n) = q * (b n - a n),
  simp, rw [add_mul, mul_add, one_mul], simp, rw [add_switch _ _ (-b n)], simp,
  rw [add_comm],
  rw [this],
  apply mul_nonneg,
  apply le_of_lt, assumption,
  rw [← le_iff_zero_le_sub], assumption,
  split,
  rw [hb], apply le_refl,
  rw [ha, hb],
  have : b n - (q * a n + (1 - q) * b n) = q * (b n - a n),
  simp, rw [add_mul, mul_add, one_mul], simp, rw [add_switch _ _ (-b n)], simp,
  rw [add_comm],
  rw [this], apply le_refl,
  have case2n := case2 n hmx,
  cases case2n with ha hb,
  split,
  rw [ha], apply le_refl,
  split,
  rw [ha, hb, le_iff_zero_le_sub],
  have : q * a n + (1 - q) * b n - a n = (1 - q) * (b n - a n),
  simp, rw [add_mul, add_mul, one_mul, one_mul, mul_add], simp,
  rw [add_comm _ (b n), add_switch _ _ (-a n), add_switch _ _ (-a n),
  add_switch _ _],
  rw [this],
  apply mul_nonneg,
  apply le_of_lt, rw [← lt_iff_zero_lt_sub], assumption,
  rw [← le_iff_zero_le_sub], assumption,
  split,
  rw [hb, le_iff_zero_le_sub],
  have : b n - (q * a n + (1 - q) * b n) = q * (b n - a n),
  simp, rw [add_mul, mul_add], simp, rw [add_switch (b n)], simp, rw [add_comm],
  rw [this],
  apply mul_nonneg,
  apply le_of_lt, assumption,
  rw [← le_iff_zero_le_sub], assumption,
  rw [ha, hb],
  have : q * a n + (1 - q) * b n - a n = (1 - q) * (b n - a n),
  simp, rw [add_mul, one_mul, add_mul, one_mul, mul_add], simp,
  rw [add_comm _ (b n), add_switch _ _ (-a n), add_switch _ _ (-a n),
  add_switch _ _ (-(q * b n))],
  rw [this],
  apply mul_le_right,
  rw [← le_iff_zero_le_sub], assumption,
  assumption,
  have propab2 : ∀ n, a n ≤ b n,
  intros n, induction n with n hr,
  rw [ha0, hb0], apply le_of_lt, assumption,
  have := (propab n hr).right.left,
  exact this,
  have propab3 := λ n, (propab n (propab2 n)).left,
  have propab4 := λ n, (propab n (propab2 n)).right.left,
  have propab5 := λ n, (propab n (propab2 n)).right.right.left,
  have propab6 := λ n, (propab n (propab2 n)).right.right.right,
  clear propab,
  cases hq with hq1 hq2,
  cases hq2 with hq2 hq3,
  have propab := tendsto_zero_upper_geom (λ n, b n - a n) q (le_of_lt _ _ hq1) hq2 propab6 _,
  cases (nested_intervals a b propab3 propab5 propab) with L hL,
  existsi L,
  split, assumption,
  split, assumption,
  split, assumption,
  split, assumption,
  split, exact hL.right.right.left,
  split, exact hL.right.right.right,
  split, exact hL.left,
  split, exact hL.right.left,
  have : ∀ n, P (a n) ∧ ¬(P (b n)),
  intros n,
  induction n with n hr,
  rw [ha0, hb0], split, assumption, assumption,
  cases (Pem (q * a n + (1 - q) * b n)) with hmx hmx,
  have case1n := case1 n hmx,
  rw [case1n.left, case1n.right],
  split, assumption, exact hr.right,
  have case1n := case2 n hmx,
  rw [case1n.left, case1n.right],
  split, exact hr.left, assumption,
  split, intros n, exact (this n).left,
  split, intros n, exact (this n).right,
  exact propab6,
  intros n, simp,
  have := propab2 n,
  rw [le_iff_zero_le_sub] at this, simp at this,
  assumption,
end

private theorem qbase_exists : ∃ q: ℝ, 0 < q ∧ q < 1 ∧ 1 - q ≤ q :=
begin
  cases r16 with q0 hq0,
  cases hq0 with hq0 hq1,
  cases le_lt_dichotomy q0 (1 - q0),
  existsi (1 - q0),
  split,
  apply lt_trans; assumption,
  split,
  rw [lt_iff_zero_lt_sub], simp, assumption,
  apply le_of_lt, rw [lt_iff_zero_lt_sub] at h ⊢, simp at h ⊢, assumption,
  existsi q0,
  split,
  assumption,
  split,
  assumption,
  assumption,
end

private def qbase := some (qbase_exists)

private theorem qbase_properties : 0 < qbase ∧ qbase < 1 ∧ 1 - qbase ≤ qbase :=
begin
  apply some_spec qbase_exists,
end

private theorem inverse_exists_pre1 (x: ℝ) : x > 0 → ∃ y, y * x > 1 :=
begin
  intro hx0,
  have h1 : ¬ (¬ ∃ y, y * x > 1),
  intro h,
  apply tec_bound x hx0,
  intros y,
  cases le_lt_dichotomy 1 (y * x) with hd,
  exfalso, apply h, existsi y, assumption,
  assumption,
  by_cases (∃ y, y * x > 1),
  assumption,
  exfalso, apply h1, assumption,
end

private theorem inverse_exists_pre2 (x: ℝ) : ∀ y: ℝ, y * x ≤ 1 ∨ ¬(y * x ≤ 1) :=
begin
  intros y,
  cases le_lt_dichotomy 1 (y * x) with hxy hxy,
  right,
  intro h,
  apply lt_irrefl, apply lt_le_trans; assumption,
  left, assumption,
end

private theorem inverse_exists_pos (x: ℝ): x > 0 → ∃ y, y * x = 1 :=
begin
  intros hx0,
  let v := some (inverse_exists_pre1 x hx0),
  have : v * x > 1,
  apply some_spec (inverse_exists_pre1 x hx0),
  have hv : ¬(v * x) ≤ 1,
  intro h, apply lt_irrefl, apply lt_le_trans 1 (v * x), exact this, assumption,
  have th := nested_interval_search (λ y, y * x ≤ 1) (inverse_exists_pre2 x) 0 v _ _ hv qbase qbase_properties,
  cases th with a ha,
  cases ha with b h,
  cases h with L hL,
  existsi L,
  cases hL with hL1 hL2,
  cases hL2 with hL2 hL3,
  cases hL3 with hL3 hL4,
  cases hL4 with hL4 hL5,
  cases hL5 with hL5 hL6,
  cases hL6 with hL6 hL7,
  cases hL7 with hL7 hL8,
  cases hL8 with hL8 hL9,
  cases hL9 with hL9 hL10,
  cases hL10 with hL10 hL11,
  have hq := qbase_properties,
  cases hq with hq0 hq1,
  cases hq1 with hq1 hq2,
  have ax_nd: ∀ n, a n * x ≤ a (n + 1) * x,
  intros n, apply mul_le_right,
  apply le_of_lt, exact hx0,
  apply hL3,
  have bx_ni: ∀ n, b (n + 1) * x ≤ b n * x,
  intros n, apply mul_le_right,
  apply le_of_lt, exact hx0,
  apply hL4,
  have g := tendsto_zero_upper_geom (λ n, b n * x - a n * x) (qbase) (le_of_lt _ _ hq0) hq1 _ _,
  have conv := nested_intervals (λ n, a n * x) (λ n, b n * x) ax_nd bx_ni g,
  cases conv with R hR,
  cases hR with hR1 hR2,
  cases hR2 with hR2 hR3,
  cases hR3 with hR3 hR4,
  have RL : R = L * x,
  cases lt_trichotomy R (L * x) with hRL hRL,
  exfalso,
  cases (hR2 (L * x - R) _) with N1 hN1,
  have hN2 := (hN1 N1 (nat.le_refl N1)).right, simp at hN2, rw [add_switch] at hN2, simp at hN2,
  rw [mul_lt_mul_right] at hN2,
  apply lt_irrefl, apply lt_le_trans, exact hN2, apply hL6,
  assumption,
  rw [lt_iff_zero_lt_sub] at hRL, assumption,
  cases hRL with hRL hRL,
  assumption,
  exfalso,
  cases (hR1 (R - L * x) _) with N1 hN1,
  have hN2 := (hN1 N1 (nat.le_refl N1)).left, simp at hN2,
  rw [mul_lt_mul_right] at hN2,
  apply lt_irrefl, apply lt_le_trans, exact hN2, apply hL5,
  assumption,
  rw [lt_iff_zero_lt_sub] at hRL,
  assumption,
  rw [← RL],
  simp at hL9 hL10,
  have hL10' : ∀ n, 1 ≤ b n * x,
  intros n, cases le_dichotomy 1 (b n * x) with hh hh,
  assumption,
  exfalso, exact (hL10 n) hh,
  cases lt_trichotomy 1 R with hhR1 hhR1,
  exfalso,
  cases (hR1 (R - 1) _) with N hN,
  have hN2 := (hN N (nat.le_refl N)).left,
  simp at hN2,
  apply lt_irrefl, apply lt_le_trans, exact hN2, apply hL9,
  rw [lt_iff_zero_lt_sub] at hhR1, assumption,
  cases hhR1 with hhR1 hhR1,
  rw [hhR1],
  exfalso,
  cases (hR2 (1 - R) _) with N hN,
  have hN2 := (hN N (nat.le_refl N)).right,
  simp at hN2, rw [add_switch] at hN2, simp at hN2,
  apply lt_irrefl, apply lt_le_trans, exact hN2, apply hL10',
  rw [lt_iff_zero_lt_sub] at hhR1, assumption,
  simp at hL11 ⊢,
  intros n,
  rw [← neg_mul, ← neg_mul, ← add_mul, ← add_mul, ← mul_assoc],
  rw [mul_le_mul_right], apply hL11,
  assumption,
  simp, intros n,
  rw [← neg_mul, ← add_mul], apply mul_nonneg,
  have : b n + -a n = b n - a n,
  simp,
  rw [this, ← le_iff_zero_le_sub],
  apply le_trans,
  apply hL5,
  apply hL6,
  apply le_of_lt, assumption,
  rw [← mul_lt_mul_right x, zero_mul],
  apply lt_trans, apply zero_lt_one, assumption,
  assumption,
  rw [zero_mul], apply le_of_lt, apply zero_lt_one,
end

theorem inverse_exists (x: ℝ) (hx: x ≠ 0): ∃ y, y * x = 1 :=
begin
  cases lt_trichotomy 0 x with ht ht,
  apply inverse_exists_pos x ht,
  cases ht with ht ht,
  exfalso, apply hx, rw [ht],
  rw [← neg_lt_neg_iff, neg_zero] at ht,
  cases (inverse_exists_pos (-x) ht) with y0 hy0,
  existsi (-y0),
  simp at hy0 ⊢,
  assumption,
end

noncomputable def inverse (x: ℝ) := if dp: x = 0 then (0: ℝ) else some (inverse_exists x dp)

theorem ne_of_lt (x y: ℝ) : x < y → x ≠ y :=
begin
  intros hx he,
  apply lt_irrefl,
  rw [he] at hx,
  assumption,
end

theorem zero_ne_one : (0: ℝ) ≠ 1 := ne_of_lt _ _ zero_lt_one

theorem ne_of_gt (x y: ℝ) : y < x → x ≠ y :=
begin
  intros hx he,
  apply lt_irrefl,
  rw [he] at hx,
  assumption,
end

theorem lt_or_gt_of_ne (x y: ℝ) : x ≠ y → x < y ∨ y < x :=
begin
  intros he,
  cases lt_trichotomy y x with ht ht,
  right,
  assumption,
  cases ht with ht ht,
  exfalso, apply he, rw [ht],
  left, assumption,
end

theorem ne_dichotomy (x y: ℝ) : x = y ∨ x ≠ y :=
begin
  cases lt_trichotomy x y with ht ht,
  right, apply ne_of_lt, assumption,
  cases ht with ht ht,
  left, assumption,
  right, apply ne_of_gt, assumption,
end

theorem inverse_is_left_inverse (x: ℝ) (hx: x ≠ 0): inverse x * x = 1 :=
begin
  unfold inverse, simp [hx],
  apply some_spec (inverse_exists x hx),
end

theorem inverse_is_right_inverse (x: ℝ) (hx: x ≠ 0): x * inverse x = 1 :=
begin
  rw [mul_comm],
  apply inverse_is_left_inverse x hx,
end

theorem left_inverse_unique : x ≠ 0 → y * x = 1 → y = inverse x :=
begin
  intros hx hxy,
  have : y * x * x.inverse = x.inverse,
  rw [hxy, one_mul],
  rw [mul_assoc, inverse_is_right_inverse x hx, mul_one] at this,
  assumption,
end

theorem right_inverse_unique : x ≠ 0 → x * y = 1 → y = inverse x :=
begin
  intros hx hxy,
  rw [mul_comm] at hxy,
  apply left_inverse_unique x y hx hxy,
end

def div (x y: ℝ) := x * (inverse y)

instance : has_div ℝ := ⟨div⟩

theorem div_def : x / y = x * (inverse y) :=
begin
  refl
end

theorem div_self : x ≠ 0 → x / x = 1 :=
begin
  rw [div_def], exact inverse_is_right_inverse _,
end

theorem inverse_is_inv : inverse x = 1 / x :=
begin
  rw [div_def, one_mul],
end

theorem div_is_mul_inv : x / y = x * (1 / y) :=
begin
  rw [div_def, inverse_is_inv],
end

@[simp] theorem div_zero : x / 0 = 0 :=
begin
  have : x / 0 = x * (inverse 0),
  refl,
  rw [this],
  simp [inverse],
end

theorem inv_zero : (1: ℝ) / 0 = 0 := div_zero _

theorem div_iff_mul (x y z: ℝ) : y ≠ 0 → (x / y = z ↔ x = y * z) :=
begin
  intros hy,
  rw [div_def],
  split; intro h,
  rw [← h, mul_comm, mul_assoc, inverse_is_left_inverse _ hy, mul_one],
  rw [h, mul_comm y, mul_assoc, inverse_is_right_inverse _ hy, mul_one],
end

@[simp] theorem zero_div : 0 / x = 0 :=
begin
  rw [div_def, zero_mul]
end

@[simp] theorem div_one : x / 1 = x :=
begin
  rw [div_iff_mul, one_mul],
  apply ne_of_gt,
  apply zero_lt_one,
end

theorem inv_one : (1: ℝ) / 1 = 1 := (div_one 1)

theorem div_mul_self : y ≠ 0 → x / y * y = x :=
begin
  intros hy,
  rw [div_def, mul_assoc, inverse_is_left_inverse, mul_one],
  assumption,
end

@[simp] theorem div_mul_div : x / y * (z / t) = x * z / (y * t) :=
begin
  cases ne_dichotomy y 0 with hty hty,
  rw [hty, zero_mul, div_zero, zero_mul, div_zero],
  cases ne_dichotomy t 0 with htt htt,
  rw [htt, mul_zero, div_zero, div_zero, mul_zero],
  apply eq.symm,
  rw [div_iff_mul, mul_comm (y * t), mul_assoc, mul_comm (z / t), ← mul_assoc,
  ← mul_assoc, div_mul_self, mul_assoc, mul_comm t, div_mul_self],
  assumption,
  assumption,
  intro hyt,
  cases (zero_product y t hyt) with h1 h1,
  exact hty h1,
  exact htt h1,
end
 
theorem inv_mul : 1 / (x * y) = 1 / x * (1 / y) :=
begin
  rw [div_mul_div, one_mul],
end

@[simp, priority 10] theorem mul_div : x * (y / z) = x * y / z :=
begin
  rw [← div_one x, div_mul_div, one_mul, div_one],
end

theorem inv_ne_zero : x ≠ 0 → 1 / x ≠ 0 :=
begin
  intros h1 h2,
  rw [div_iff_mul, mul_zero] at h2,
  apply zero_ne_one, rw [h2], assumption,
end

theorem inv_inv : 1 / (1 / x) = x :=
begin
  cases ne_dichotomy x 0 with hd hd,
  rw [hd], simp,
  rw [div_iff_mul, div_mul_self], assumption,
  apply inv_ne_zero, assumption,
end

theorem inv_div : 1 / (x / y) = y / x :=
begin
  rw [div_is_mul_inv x, inv_mul, inv_inv, mul_comm, ← div_is_mul_inv],
end

@[simp, priority 10] theorem div_div : x / (y / z) = x * z / y :=
begin
  rw [div_is_mul_inv, inv_div, mul_div],
end

@[simp, priority 10] theorem div_mul : x / y * z = x * z / y :=
begin
  rw [mul_comm], simp, rw [mul_comm],
end

@[simp] theorem div_div_div : x / y / (z / t) = x * t / (y * z) :=
begin
  simp, rw [← mul_div, ← mul_div, div_is_mul_inv, div_mul_div, ← mul_div, ← mul_assoc, mul_div (x * t), mul_one],
end

theorem mul_ne_zero : x * y ≠ 0 ↔ x ≠ 0 ∧ y ≠ 0 :=
begin
  split; intros h,
  split; intros hh,
  rw [hh, zero_mul] at h, exact h (eq.refl _),
  rw [hh, mul_zero] at h, exact h (eq.refl _),
  cases h with hl hr,
  intros h,
  have := zero_product _ _ h,
  cases this,
  apply hl, assumption,
  apply hr, assumption,
end

theorem mul_eq_zero : x * y = 0 ↔ x = 0 ∨ y = 0 :=
begin
  split; intros h,
  exact zero_product _ _ h,
  cases h with hl hr,
  rw [hl, zero_mul],
  rw [hr, mul_zero],
end

theorem div_simp_num_den : z ≠ 0 → x * z / (y * z) = x / y :=
begin
  intros hx,
  rw [← div_mul_div],
  rw [div_self _ hx, mul_one],
end

theorem div_simp_num : y ≠ 0 → x * y / y = x :=
begin
  have : x * y / y = x * y / (1 * y),
  rw [one_mul],
  rw [this],
  intros h,
  rw [div_simp_num_den _ _ _ h, div_one],
end

theorem div_simp_den : y ≠ 0 → y / (x * y) = 1 / x :=
begin
  intros h,
  have : y / (x * y) = (1 * y) / (x * y),
  rw [one_mul],
  rw [this, div_simp_num_den], assumption,
end

theorem div_add_div {x y z t: ℝ} : y ≠ 0 → t ≠ 0 → x / y + z / t = (x * t + y * z) / (y * t) :=
begin
  intros hy ht,
  symmetry,
  rw [div_iff_mul, mul_add, mul_assoc, mul_comm _ (t * (x / y)), mul_assoc,
  mul_assoc, div_mul, div_simp_num, mul_div, mul_comm t z, div_simp_num,
  mul_comm],
  assumption, assumption, rw [mul_ne_zero], split; assumption,
end

theorem add_div {x y z: ℝ} : z ≠ 0 → x + y / z = (x * z + y) / z :=
begin
  intros hz,
  have : x + y / z = x / 1 + y / z,
  rw [div_one],
  rw [this, div_add_div, one_mul, one_mul],
  apply ne_of_gt, apply zero_lt_one,
  assumption,
end

@[simp] theorem neg_div : -(x / y) = -x / y :=
begin
  cases ne_dichotomy y 0 with hd hd,
  rw [hd], simp,
  rw [← add_right_inj (x / y), div_add_div], simp,
  rw [mul_comm y x], simp,
  assumption, assumption,
end

theorem sub_div {x y z: ℝ} : z ≠ 0 → x - y / z = (x * z - y) / z :=
begin
  intros hz,
  simp,
  apply add_div,
  assumption,
end

theorem div_sub_div {x y z t: ℝ} : y ≠ 0 → t ≠ 0 → x / y - z / t = (x * t - y * z) / (y * t) :=
begin
  intros hy ht,
  simp, rw [div_add_div], simp,
  assumption, assumption,
end

theorem inv_pos : 0 < x → 0 < 1 / x :=
begin
  intros h,
  rw [← mul_lt_mul_right x], simp, rw [div_self],
  apply zero_lt_one,
  apply ne_of_gt, assumption,
  assumption,
end

theorem inv_pos_dec : 0 < x → x < y → 1 / y < 1 / x :=
begin
  intros hx hxy,
  rw [← mul_lt_mul_right (x * y), ← mul_assoc (1 / x)], simp,
  rw [div_simp_num, mul_comm, div_simp_num],
  assumption, apply ne_of_gt, assumption, apply ne_of_gt,
  apply lt_trans; assumption,
  apply mul_pos, assumption, apply lt_trans; assumption,
end

theorem inv_of_gt_one : 1 < x → 0 < 1 / x ∧ 1 / x < 1 :=
begin
  intros hx,
  split,
  apply inv_pos, apply lt_trans, exact zero_lt_one, assumption,
  have hx' := inv_pos_dec 1 x zero_lt_one hx,
  simp at hx', assumption,
end

-- the least upper bound property
-- after this, we can be sure that ℝ is
-- (classically) isomorphic to the field of real numbers.

-- subsets S of ℝ are implemented as functions ℝ → bool
-- an element of ℝ being considered in S iff its image is tt

theorem lub_property (f: ℝ → bool) :
  (∃ x, f x = tt)
  → (∃ A, ∀ x: ℝ, f x = tt → x ≤ A)
  → ∃ L,
     (∀ x: ℝ, f x = tt → x ≤ L)
     ∧ (∀ ε > 0, ∃ x, f x = tt ∧ L - ε < x) :=
begin
  let P : ℝ → Prop := λ a, ∃ x, f x = tt ∧ a ≤ x,
  intros h1 h2,
  cases h1 with u hu,
  cases h2 with w hw,
  have ni := nested_interval_search P _ u (w + 1) _ _ _ (1 / (1 + 1)) _,
  cases ni with a ha,
  cases ha with b hb,
  cases hb with L ni2,
  cases ni2 with ni2 ni3,
  cases ni3 with ni3 ni4,
  cases ni4 with ni4 ni5,
  cases ni5 with ni5 ni6,
  cases ni6 with ni6 ni7,
  cases ni7 with ni7 ni8,
  cases ni8 with ni8 ni9,
  cases ni9 with ni9 ni10,
  cases ni10 with ni10 ni11,
  cases ni11 with ni11 ni12,
  existsi L,
  split,
  intros x hx,
  cases le_lt_dichotomy L x with hd hd,
  exfalso,
  cases (ni9 (x - L) _) with N hN,
  have hN' := (hN N (nat.le_refl N)).right,
  simp at hN', rw [add_comm] at hN', simp at hN',
  apply ni11 N,
  existsi x,
  split, assumption, apply le_of_lt, assumption,
  rw [lt_iff_zero_lt_sub] at hd, exact hd,
  assumption,
  intros ε hε,
  have hh := ni8 ε hε,
  cases hh with N hN,
  have hh := (hN N (nat.le_refl N)).left,
  have hhh := ni10 N,
  cases hhh with x hx,
  existsi x,
  cases hx,
  split,
  assumption,
  simp,
  apply lt_le_trans; assumption,
  intros x,
  by_cases (P x), left, assumption, right, assumption,
  have hh := hw u hu,
  apply le_lt_trans, assumption,
  rw [lt_iff_zero_lt_sub], simp, rw [add_comm], simp, apply zero_lt_one,
  existsi u,
  split, assumption, apply le_refl,
  intros hP,
  cases hP with x hx,
  cases hx with h1 h2,
  have hh := hw _ h1,
  have hhh := le_trans _ _ _ h2 hh,
  rw [le_iff_zero_le_sub] at hhh, simp at hhh,
  rw [← add_le_add_left 1] at hhh,
  simp at hhh,
  apply lt_irrefl, apply le_lt_trans _ 0, assumption, apply zero_lt_one,
  have := inv_of_gt_one (1 + 1) _,
  cases this with h1 h2,
  split, assumption,
  split, assumption,
  rw [sub_div], simp,
  apply le_refl,
  apply ne_of_gt,
  apply lt_trans _ 1,
  apply zero_lt_one,
  rw [lt_iff_zero_lt_sub], simp, apply zero_lt_one,
  rw [lt_iff_zero_lt_sub], simp, apply zero_lt_one,
end

#print axioms lub_property
end real
