import tactic
import data.real.basic
import data.set

/--
Definition for convergence of a sequence a n to a limit t.
-/
def tendsto (a : ℕ → ℝ) (t : ℝ) : Prop :=
∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

/--
Lemma for rewriting tendsto without using the change tactic.
-/
lemma tendsto_def {a : ℕ → ℝ} {t : ℝ} :
  tendsto a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε :=
begin
  refl
end


/--
A sequence a n tends to t iff -a n tends to -t.
This is a problem from the problem sheets converted to an iff.
-/
theorem tendsto_neg_iff {a : ℕ → ℝ} {t : ℝ} :tendsto a t ↔ tendsto (λ n, - a n) (-t) :=
begin
  split,
  intro ha,
  rw tendsto_def at ⊢ ha,
  intro eps,
  intro he,
  specialize ha eps,
  have hb : (∃ (B : ℕ), ∀ (n : ℕ), B ≤ n → |a n - t| < eps),
  apply ha, exact he,
  cases hb,
  use hb_w,
  intro n,
  intro i,
  rw ←abs_neg (- a n - -t),
  ring_nf,
  apply hb_h,exact i,

  intro ha,
  rw tendsto_def at ⊢ ha,
  intro eps,
  intro he,
  specialize ha eps,
  have hb: (∃ (B : ℕ), ∀ (n : ℕ), B ≤ n → | -a n - -t| < eps),
  apply ha, exact he,
  cases hb,
  use hb_w,
  intros n i,
  specialize hb_h n,
  rw ←abs_neg (a n  -t),
  ring_nf,
  ring_nf at hb_h,
  apply hb_h, exact i,
end
#lint