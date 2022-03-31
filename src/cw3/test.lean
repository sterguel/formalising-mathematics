import tactic
import data.real.basic
import data.int.basic
import data.int.parity
example (a b c : ℝ   )  : |a| < |b| → a^2 < b^2:= begin
  exact sq_lt_sq,
end
example (a b : ℝ  ) : b ≤  |b| :=
begin
  exact le_abs_self b,
end

example (a b c: ℚ) (h : a < b) (h2: 0 < c) : c * a < c * b :=
begin
  library_search,
end

example (a : ℚ) : 0 ≠ a → 0 ≤ a → 0 < a :=
begin
  intros h i,
  library_search,
end

example (a b: ℚ) : a ≠ b ↔ ¬ (a = b) := begin
  exact iff.rfl,
end


example ( a b : ℚ) (h: b ≠ 0): b * (a / b ) = a :=
begin
  exact mul_div_cancel' a h,
end
--zify is useful!!
--mod_cast norm_cast


example (a b: ℤ  ) (h: odd b) (h2: a ∣ b) : odd a :=
begin
  cases h2,
  rw h2_h at h,
  rw int.odd_mul at h,
  exact h.left,
end

example (x y : ℤ): x*y = 0 → x = 0 ∨ y = 0:=
begin
  intro h,
  exact zero_eq_mul.mp (eq.symm h),
  
end

example (P : Prop) : P ∨ P → P:=
begin
  library_search,
end