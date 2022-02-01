import tactic
import data.real.basic
import data.set
import reals_ps


def monotone_increasing (a : ℕ → ℝ) : Prop :=
∀(n : ℕ), a (n+1) ≥ a n

theorem monotone_increasing_def {a : ℕ → ℝ} :
  monotone_increasing a ↔ ∀(n : ℕ), a (n+1) ≥ a n := by refl

-- I realise now that defining it this way may not have been such a good idea.
lemma monotone_increasing_add {a : ℕ → ℝ}:
 monotone_increasing a → ∀(n : ℕ), ∀ (m : ℕ),a (m+n) ≥ a n :=
begin
  intro h,
  intros n m,
  induction m,
  rw zero_add,
  norm_num,
  rw nat.succ_eq_one_add,
  have h2: a ( (m_n + n) + 1) ≥ a (m_n + n),
  rw monotone_increasing_def at h,
  specialize h (m_n + n),
  exact h,
  rw add_assoc,
  rw add_comm,
  linarith,
end

theorem monotone_increasing_ind {a : ℕ → ℝ}:
monotone_increasing a ↔ ∀(n : ℕ), ∀ (m : ℕ), m ≥ n → a m ≥ a n :=
begin
  split,
  {
    intro h,
    intros n m,
    intro h2,
    have h3 : ∃ (r: ℕ), n + r = m,
    use m - n,
    linarith,
    cases h3 with s hs,
    rw ←hs,
    rw add_comm,
    apply monotone_increasing_add, exact h,
  },
  {
    intro h,
    intro n,
    specialize h n (n+1),
    apply h,
    norm_num,
  }
end

def monotone_decreasing (a : ℕ → ℝ) : Prop := 
  ∀(n : ℕ), a (n+1) ≤ a n

theorem monotone_decreasing_def {a : ℕ → ℝ} :
  monotone_increasing a ↔ ∀(n : ℕ), a (n+1) ≥ a n := by refl

def strictly_increasing (a : ℕ → ℕ) : Prop :=
  ∀(n : ℕ), a (n + 1) > a n



theorem bdd_inc_seq_converges {a : ℕ → ℝ} (hb: ∃(M:ℝ), ∀(n: ℕ), a n ≤ M) (hm : monotone_increasing a): ∃(l : ℝ), tendsto a l :=
begin
  let S := set.range a,
  have hsb : bdd_above S, --Prove that S is bounded above
  cases hb with M hbh,
  use M,
  intro a,
  intro as,
  rw set.mem_range at as,
  cases as with ay,
  specialize hbh ay,
  rw ←as_h,
  exact hbh,
  let t := Sup S,
  use t, -- this is the limit
  intro eps,
  intro heps,
  let d := t - eps/2,
  have hds : d ≤ t,
  norm_num,
  linarith,
  rw real.le_Sup_iff at hds,
  {
    specialize hds (-eps/2), --go at most epsilon away from the supremum
    have hxs: (∃ (x : ℝ) (H : x ∈ S), d + -eps/2 < x), apply hds, linarith,
    cases hxs with x hxsi,
    cases hxsi with xs hxs_h,
    rw set.mem_range at xs,
    cases xs with b,
    use b,
    intro n,
    intro hbn,
    have han_ab: a n ≥ a b,
    rw monotone_increasing_ind at hm,
    specialize hm b n,
    apply hm,
    exact hbn,
    rw abs_sub_comm (a n) t,
    have hnomod: |t - a n| = t - a n, -- remove the modulus so linarith works
    rw abs_eq_self,
    rw sub_nonneg,
    apply le_cSup, 
    exact hsb,
    rw set.mem_range,
    use n,
    rw hnomod,
    rw ←xs_h at hxs_h,
    change  t - eps/2 + -eps / 2 < a b at hxs_h,
    linarith,
  },
  {exact hsb,}, --bounded above is a hypothesis, for some reason this comes after the main goal??
  { --S is non empty
    use a 1,
    rw set.mem_range,
    use 1,
  }
end

theorem bdd_dec_seq_converges {a : ℕ → ℝ} (hb: ∃(M:ℝ), ∀(n: ℕ), a n ≥ M) (hm : monotone_decreasing a): ∃(l : ℝ), tendsto a l :=
begin
  -- recycle the proof and combine with the tendsto_neg (modified to be an iff so we can go both ways)
  let b := (λ n, - a n),
  have hi: monotone_increasing b,
  intro n,
  specialize hm n,
  change -a (n + 1) ≥ -a n,
  norm_num, exact hm,
  cases hb,
  have hbt: ∃(M:ℝ), ∀(n: ℕ), b n ≤ M,
  use -hb_w,
  change ∀ (n : ℕ), -a n ≤ -hb_w,
  intro n,
  specialize hb_h n,
  norm_num, exact hb_h,
  have hbc: ∃(s : ℝ), tendsto b s,
  apply bdd_inc_seq_converges,
  exact hbt,
  exact hi,
  cases hbc with nl hnl,
  use -nl,
  rw tendsto_neg_iff,
  rw neg_neg,
  exact hnl,
end

def peak (a : ℕ → ℝ) (i : ℕ) : Prop:=
  ∀(n : ℕ), n > i → a n > a i


theorem bolzano_weierstrass {a : ℕ → ℝ} (hb: ∃(M:ℝ), ∀(n: ℕ), |a n| ≤ M) :
∃(n: ℕ → ℕ) (hn: strictly_increasing n) (l : ℝ), tendsto (λ t, a (n t)) l :=
begin
  by_cases (∀(t : ℕ), ∃(u: ℕ), u > t ∧ peak a u),
  {
    sorry,
  },{
    sorry,
  }
end 