import tactic
import analysis.inner_product_space.basic
import data.set
import data.real.basic
variables {V : Type*} [inner_product_space ℝ V] [finite_dimensional ℝ V] (T : V →ₗ[ℝ] V ) (h_non_triv_space : ∃ (v : V), v ≠ 0)

def S : set ℝ := {x : ℝ | ∃ (y : V), (y ≠ 0) ∧ (λ (x : V) , ∥T x∥/∥x∥) y = x}
def S2 : set ℝ := {x : ℝ | ∃ (y : V), (λ (x : V) , ⟪T x, T x⟫_ℝ/⟪x, x⟫_ℝ) y = x}

example : ∀ (v : V), ⟪v, v⟫_ℝ = ∥v∥^2 :=
begin
  intro v,
  rw real_inner_self_eq_norm_mul_norm,
  ring,
end

lemma S2_map_nonneg : ∀(x : V), x ≠ 0 → 0 ≤ ⟪T x, T x⟫_ℝ / ⟪x, x⟫_ℝ:=
begin
  intro x,
  intro h,
  have h2: 0 ≤ ⟪T x, T x⟫_ℝ,
  exact real_inner_self_nonneg,
  have h3 : 0 < ⟪x,x⟫_ℝ,
    have h4: 0 ≠ ⟪x,x⟫_ℝ,
      by_contra h3,
      rw eq_comm at h3,
      rw inner_self_eq_zero at h3,
      apply h, exact h3,
    rw ne_iff_lt_or_gt at h4,
    cases h4,
      exact h4,
      exfalso,
      change ⟪x,x⟫_ℝ < 0 at h4,
      rw ←not_le at h4,
      apply h4,
      exact real_inner_self_nonneg,
  rw le_div_iff,
  rw zero_mul, exact h2,
  exact h3,
end

lemma S_map_nonneg: ∀(x : V), x ≠ 0 → 0 ≤ ∥T x∥/∥x∥:=
begin
  intro x,
  intro h,
  rw norm_eq_sqrt_real_inner,
  rw norm_eq_sqrt_real_inner,
  rw ←real.sqrt_div,
  rw ←real.sqrt_zero,
  apply real.sqrt_le_sqrt,
  apply S2_map_nonneg,
  exact h,
  exact real_inner_self_nonneg,
end

lemma V_nonempty : nonempty V :=
begin
  exact has_zero.nonempty,
end

lemma max_squared {h: is_lub (S2 T) (Sup (S2 T))} (h_non_triv_space : ∃ (v : V), v ≠ 0): is_lub (S T) (real.sqrt (Sup (S2 T))) := 
begin
  cases h with hup hleast,
  have hup2: real.sqrt (Sup (S2 T)) ∈ upper_bounds (S T),
  {
    change ∀⦃a : ℝ⦄, a ∈ (S T) → a ≤  real.sqrt (Sup (S2 T)),
    intro a,
    intro h2,
    change ∃(y : V), (y ≠ 0) ∧ ∥T y∥/∥y∥  = a at h2,
    cases h2,
    cases h2_h with h2_h_nz h2_h,
    rw norm_eq_sqrt_real_inner at h2_h,
    rw norm_eq_sqrt_real_inner at h2_h,
    rw ←real.sqrt_div at h2_h,
    {
      rw ←h2_h,
      rw real.sqrt_le_sqrt_iff,
      apply le_cSup,
      use Sup (S2 T), exact hup,
      use h2_w,
      apply le_cSup_of_le,
      use Sup (S2 T), exact hup,
      use h2_w,
      apply S2_map_nonneg, exact h2_h_nz,
    },{
      exact real_inner_self_nonneg,
    }
  },
  split,
    exact hup2,
  change ∀ ⦃a : ℝ⦄, a ∈ upper_bounds (S T) → real.sqrt (Sup (S2 T)) ≤ a,
  intro a,
  intro h,
  change ∀⦃b : ℝ⦄, b ∈ (S T) → b ≤  a at h,
  by_contra h2,
  rw not_le at h2,
  let b := a^2,
  have h3: b < Sup (S2 T),
  rw ←real.sqrt_lt_sqrt_iff,
  rw real.sqrt_sq,
  exact h2,
  cases h_non_triv_space with vnz hv,
  have h4 := S_map_nonneg,
  specialize h4 T,
  specialize h4 vnz,
  have h5 : 0 ≤ ∥T vnz∥ / ∥vnz∥,
  apply h4, exact hv,
  have h6 : ∥T vnz∥ / ∥vnz∥ ≤ a,
  have h7 :  ∥T vnz∥ / ∥vnz∥ ∈ (S T),
  use vnz, split, exact hv, refl,
  apply h, exact h7, linarith [h5,h6],
  exact _inst_2,
  exact sq_nonneg a,
  
end

example (a : ℝ): 0 ≤ a^2 :=
begin
  exact sq_nonneg a,
end