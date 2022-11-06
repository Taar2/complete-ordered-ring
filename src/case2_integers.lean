noncomputable theory

/- This one proves that a ring with axioms r1-r15,
   0 ≠ 1, and nothing between 0 and 1,
   is actually ℤ in disguise.

   This uses classical reasoning.

   r2 and r12 aren't used.
-/

/- Maybe r15 isn't necessary?

   See http://matwbn.icm.edu.pl/ksiazki/fm/fm85/fm85114.pdf ?
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

axiom r16: (0: ℝ) < 1 ∧ ¬(∃ x: ℝ, 0 < x ∧ x < 1)

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
  exact r16.left,
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

def sub (x y: ordring) : ordring := x + (-y)
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

--main result
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

theorem step_1 : ¬(∃ A > 0, ∀ (n: ℕ), nat_cast n ≠ A) :=
begin
  intro hA,
  cases hA with A hA,
  cases hA with hA hh,
  have hhr : ∀ n, nat_cast n < A,
  intros n,
  induction n with n hr,
  rw [nat_cast_respects_zero], assumption,
  cases lt_trichotomy (nat_cast n.succ) A with ht ht,
  assumption,
  cases ht with ht ht,
  exfalso, apply (hh n.succ), assumption,
  exfalso,
  rw [nat_cast_respects_succ] at ht,
  rw [← add_lt_add_left (- (nat_cast n))] at hr ht,
  simp at hr ht,
  apply r16.2,
  existsi (-nat_cast n + A),
  split; assumption,
  have hm := r15 (λ n, nat_cast n) _ _,
  cases hm with L hL,
  cases (hL 1 zero_lt_one) with N hN,
  simp at hN,
  have hm': ∀ n > N, (-L) + nat_cast n = 0,
  intros n hn,
  cases (hN n hn) with hn1 hn2,
  rw [← add_lt_add_left (-L)] at hn1 hn2,
  simp at hn1 hn2,
  cases lt_trichotomy (-L + nat_cast n) 0 with ht ht,
  exfalso,
  rw [← add_lt_add_left 1] at hn1 ht,
  simp at hn1 ht,
  apply r16.2,
  existsi (1 + -L + nat_cast n), split; assumption,
  cases ht with ht ht,
  assumption,
  exfalso,
  apply r16.2,
  existsi (-L + nat_cast n),
  split; assumption,
  have hm1 := hm' (N.succ) _,
  have hm2 := hm' (N.succ.succ) _,
  rw [nat_cast_respects_succ] at hm2,
  rw [← add_assoc, hm1, zero_add] at hm2,
  have hm3 := r16.1,
  rw [hm2] at hm3,
  apply lt_irrefl, assumption,
  apply nat.lt_trans, apply nat.lt_succ_self, apply nat.lt_succ_self,
  apply nat.lt_succ_self,
  intros n,
  simp,
  rw [nat_cast_respects_add, nat_cast_respects_one, add_comm],
  rw [lt_iff_zero_lt_sub], simp, apply r16.1,
  existsi A,
  simp,
  assumption,
end

--now we start reasoning classically
theorem step_2: ∀ A > 0, ∃ n, nat_cast n = A :=
begin
  intros A hA,
  by_cases (∃ (n: ℕ), nat_cast n = A),
  assumption,
  exfalso,
  apply step_1,
  existsi A, existsi hA,
  intros n hn,
  apply h,
  existsi n, assumption,
end

-- Surjectivity of int_cast.
---Combined with the injectivity
-- of int_cast (theorem int_cast_respects_lt),
-- and the fact that int_cast is a ring homomorphism
-- (theorems int_cast_respects_add, int_cast_respects_mul,
-- int_cast_respects_zero, int_cast_respects_one),
-- this gives the wanted result.
theorem final: ∀ x, ∃ n, int_cast n = x :=
begin
  have f1: ∀ x > 0, ∃ n, int_cast n = x,
  intros x hx,
  have s := step_2 x hx,
  cases s with n hn,
  existsi (int.of_nat n),
  rw [int_cast_of_nat], assumption,
  intros x,
  cases lt_trichotomy 0 x with ht ht,
  exact f1 x ht,
  cases ht with ht ht,
  rw [← ht],
  existsi (0: ℤ),
  apply int_cast_respects_zero,
  rw [← neg_lt_neg_iff, neg_zero] at ht,
  rw [← neg_neg x],
  cases (f1 (-x) ht) with n hn,
  existsi (-n),
  rw [int_cast_respects_neg, hn],
end

#print axioms final
end ordring
