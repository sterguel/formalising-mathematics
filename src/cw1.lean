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
  ∀(n : ℕ), n > i → a n < a i

def recursive (f : ℕ → ℕ) (i : ℕ) : ℕ → ℕ
| 0       :=  f i
| (x + 1) :=  f (recursive x)


theorem bolzano_weierstrass {a : ℕ → ℝ} (hb: ∃(M:ℝ), ∀(n: ℕ), |a n| ≤ M) :
∃(n: ℕ → ℕ) (hn: strictly_increasing n) (l : ℝ), tendsto (λ t, a (n t)) l :=
begin
  by_cases (∀(t : ℕ), ∃(u: ℕ), u > t ∧ peak a u),
  {
    choose r hr using h,
    let s := recursive r 0,
    have hinc : strictly_increasing s,
    {
      intro n,
      specialize hr (s n),
      cases hr with hi,
      exact hi,
    },
    --Prove that every point in the subsequence is a peak.
    --The hypothesis hr is not quite what we need since given s(n) it tells us that s(n+1) is a peak.
    have hpeak: ∀(n : ℕ), peak a (s n),{ 
      intro n,
      by_cases n = 0,
      rw h,
      change peak a (r 0),
      specialize hr 0,
      cases hr,
      exact hr_right,
      have h2 : ∃ (c : ℕ), n = c.succ,
      apply nat.exists_eq_succ_of_ne_zero,
      exact h,
      cases h2,
      rw h2_h,
      change peak a (r (s h2_w)),
      specialize hr (s h2_w),
      cases hr,
      exact hr_right,
    },
    have hsmi : monotone_decreasing (λ t, a (s t)),
    {
      intro n,
      change a ( s ( n + 1)) ≤ a ( s n ),
      specialize hpeak n,
      specialize hpeak (s (n + 1)),
      specialize hinc n,
      have g: a (s (n + 1)) < a (s n),
      apply hpeak, exact hinc,
      linarith,
    },
    use s,
    split,
    exact hinc,
    apply bdd_dec_seq_converges,
    cases hb,
    use -hb_w,
    intro n,
    specialize hb_h (s n),
    exact neg_le_of_abs_le hb_h,
    exact hsmi,
  },{
    have h2: ∃ (p : ℕ), ∀ (q : ℕ), p < q → (∃ (n : ℕ), q < n ∧ a q ≤ a n),
    --Some logic to get this into a form that is easier to work with.
    {
      rw not_forall at h, cases h,
      use h_w, rw not_exists at h_h,
      intro q,
      specialize h_h q,
      rw not_and at h_h,
      intro hnq,
      have hp: ¬peak a q,
      apply h_h, exact hnq,
      change ¬(∀(n : ℕ), n > q → a n < a q) at hp,
      rw not_forall at hp,
      cases hp,
      use hp_w,
      rw ←not_lt,
      rw ←not_le,
      rw ←not_or_distrib,
      rw ←not_lt,
      rw gt_iff_lt at hp_h,
      rw ←imp_iff_not_or,
      exact hp_h
    },
    --More tinkering so that the hypothesis works for choose.
    cases h2 with p h3,
    have h4: ∀ (r : ℕ), ∃ (n : ℕ), r < n ∧ a (r + (p+1)) ≤ a (n+ (p+1)),
    intro r, specialize h3 (r + (p+1)),
    have h5: (∃ (n : ℕ), r + (p+1) < n ∧ a (r + (p+1)) ≤ a n),
    apply h3,
    rw add_comm,
    rw add_assoc,
    rw lt_add_iff_pos_right,
    exact nat.zero_lt_one_add r,
    cases h5,
    cases h5_h,
    use h5_w - (p + 1),
    split,
    rw lt_tsub_iff_right,
    exact h5_h_left,
    have h6: h5_w - (p + 1) + (p + 1) = h5_w,
    apply nat.sub_add_cancel,
    linarith [h5_h_left],
    rw h6,
    exact h5_h_right,
    -- Construct the subsequence
    choose b hbs using h4,
    let c := recursive b 0,
    let s := (λ n, c n + (p + 1)),
    
    have hinc : strictly_increasing s,
    {
      intro n,
      specialize hbs (c n),
      cases hbs,
      change s n < s (n + 1),
      rw add_lt_add_iff_right,
      exact hbs_left,
    },
    -- Prove that it's monotone to use the theorem at the start
    have hmi : monotone_increasing (λ n, a (s n)),
    {
      intro n,
      change a (c n + (p + 1)) ≤ a (c (n + 1) + (p + 1)),
      specialize hbs (c n),
      cases hbs,
      exact hbs_right,
    },
    use s,
    split,
    exact hinc,
    apply bdd_inc_seq_converges,
    cases hb,
    use hb_w,
    intro n,
    specialize hb_h (s n),
    apply le_of_abs_le,
    exact hb_h,
    exact hmi,
  }
end 