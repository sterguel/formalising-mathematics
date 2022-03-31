import tactic
import data.int.parity
-- These are some helpful lemmas for coursework 3.
-- The main result in this file is the first theorem.

/-
A nonempty set of integers with a lower bound has a minimum.
-/
theorem bdd_below_Z_set_has_minimum {S : set ℤ} (hne : set.nonempty S) (hbdd : bdd_below S) : 
∃ (m ∈ S), ∀(n ∈ S), m ≤ n :=
begin
  cases hne with m hm,
  change ∃ x, ∀ y ∈ S, x ≤ y  at hbdd,
  cases hbdd with lb hlb,
  have hml : lb ≤ m,
  {
    specialize hlb m,
    apply hlb,
    exact hm,
  },
  let T := finset.finite_to_set(finset.Icc lb m),
  let u := set.finite.inter_of_left T S,
  let V := set.finite.to_finset u,
  have minv : m ∈ V,
  {
    rw set.finite.mem_to_finset,
    split,
    {
      suffices : m ∈ (finset.Icc lb m),
      exact finset.mem_coe.mpr this,
      rw finset.mem_Icc,
      split, exact hml, refl,
    },
    exact hm,
  },
  have hnv : V.nonempty,
  {
    use m,
    exact minv,
  },
  let M := finset.min' V hnv,
  have hMm : M ≤ m,
  {
    have h2 := finset.min'_le V m minv,
    exact h2,
  },
  use M,
  split,
  {
    have h2 := finset.min'_mem V hnv,
    rw set.finite.mem_to_finset at h2,
    exact h2.right,
  },
  {
    intros n hn,
    by_cases n ≤ m,
    {
      apply finset.min'_le,
      rw set.finite.mem_to_finset,
      split,
      {
        rw finset.mem_coe,
        rw finset.mem_Icc,
        specialize hlb n,
        split,
        apply hlb, exact hn,
        exact h,
      },
      {
        exact hn,
      },
    },
    {
      rw not_le at h,
      linarith [h, hMm],
    }
  }
end

lemma le_abs_le {a b : ℚ} (h: a ≤  b):a ≤  |b| :=
begin
  have h2 := le_abs_self b,
  linarith,
end

namespace int
lemma odd_div {a b :ℤ} : a ∣ b → odd b → odd a :=
begin
  intros h1 h2,
  cases h1 with u hu,
  rw hu at h2,
  rw odd_mul at h2,
  exact h2.left,
end

end int

lemma sqrt_one_eqn (a : ℤ) : a^2 = 1 ↔ a = 1 ∨ a = -1 :=
begin
  split,
  {
    intro h,
    apply_fun (λ x, x - (1 : ℤ)) at h,
    rw (by ring : 1 - 1 = (0 : ℤ )) at h,
    rw (by ring: a^2 - 1 = (a + 1) * (a - 1)) at h,
    rw eq_comm at h,
    rw zero_eq_mul at h,
    cases h,
      right, linarith,
      left, linarith,
  },
  {
    intro h,
    cases h;
    rw h; norm_num,
  }
end

#lint