import tactic
import cw3.euclidean_domain
import cw3.ufd
import data.int.parity
import algebra.order.archimedean

/--
The type of Gaussian Integers ℤ[i]
-/
@[nolint has_inhabited_instance]
structure gaussian_ints :=
(re : ℤ)
(im : ℤ)

attribute [ext] gaussian_ints

namespace gaussian_ints


/--
Component wise addition
-/
def add (x y : gaussian_ints) : gaussian_ints :=
⟨x.re + y.re, x.im + y.im ⟩
instance : has_add gaussian_ints :=
{ add := add }

/--
Complex multiplication
-/
def prod (x y : gaussian_ints) : gaussian_ints := 
⟨ x.re * y.re - x.im * y.im , x.re * y.im + x.im * y.re ⟩ 
instance : has_mul gaussian_ints :=
{ mul := prod }
lemma mul_def (x y : gaussian_ints) : 
x * y = ⟨ x.re * y.re - x.im * y.im , x.re * y.im + x.im * y.re ⟩ := rfl
lemma mul_re (x y : gaussian_ints):
(x*y).re = x.re * y.re - x.im * y.im := rfl
lemma mul_im (x y : gaussian_ints):
(x*y).im = x.re * y.im + x.im * y.re:= rfl

/--
Convert an integer x to x + 0i
-/
def convert_int (x : ℤ) : gaussian_ints := ⟨x , (0 : ℤ) ⟩ 

instance : has_zero gaussian_ints :=
{zero := convert_int (0:ℤ)}
instance : has_one gaussian_ints :=
{one := convert_int (1:ℤ)}

/--
Complex negation (component-wise)
-/
def neg (x : gaussian_ints) : gaussian_ints := ⟨-x.re, -x.im⟩
instance : has_neg gaussian_ints :=
{ neg := neg }

/--
Component wise subtraction
-/
def sub (x y : gaussian_ints) : gaussian_ints :=
⟨x.re - y.re, x.im - y.im ⟩
instance : has_sub gaussian_ints :=
{ sub := sub }

/--
Complex conjugation
-/
def conj (x : gaussian_ints) : gaussian_ints := ⟨ x.re, -x.im ⟩

@[nolint doc_blame]
def nsmul : ℕ → gaussian_ints → gaussian_ints
| 0 x := (0 : gaussian_ints)
| (n + 1) x := x +(nsmul n x)

@[nolint doc_blame]
def zsmul : ℤ → gaussian_ints → gaussian_ints
| (int.of_nat a) x := nsmul a x
| -[1+ a] x := -(nsmul (a + 1) x)

@[nolint doc_blame]
def npow : ℕ → gaussian_ints → gaussian_ints
| 0 x := 1
| (n+1) x := x * (npow n x)

instance : has_coe ℤ gaussian_ints :=
{ coe := convert_int }


@[simp] lemma coe_mul (x y : ℤ) : coe (x*y) = (x : gaussian_ints ) * (y:gaussian_ints) :=
begin
  ext,
  change x*y = x * y - 0 * 0,
  ring,
  change 0 * 0 = x * 0 + 0 * y,
  ring,
end

lemma ext_eq {x y : gaussian_ints} : x = y ↔ x.re = y.re ∧ x.im = y.im :=
begin
  split,
  {
    intro h,
    split;
    rw h,
  },
  {
    intro h,
    ext,
    exact h.left, 
    exact h.right,
  }
end

/-
The Gaussian integers ℤ[i] are a ring.
-/
instance : comm_ring gaussian_ints :=
{ add := add,
  add_assoc := begin
    intros a b c,
    ext,
    {
      change (a.re+b.re ) + c.re =(a.re + (b.re + c.re)),
      ring,
    },
    {
      change (a.im+b.im ) + c.im =(a.im + (b.im + c.im)),
      ring,
    },
  end,
  zero := convert_int 0,
  zero_add := begin
    intro a,
    ext,
    {
      change (0 : ℤ) + a.re = a.re,
      rw zero_add,
    },
    {
      change (0 : ℤ) + a.im = a.im,
      rw zero_add,
    }
  end,
  add_zero := begin
    intro a,
    ext,
    {
      change  a.re + (0 : ℤ) = a.re,
      rw add_zero,
    },
    {
      change a.im + (0 : ℤ) = a.im,
      rw add_zero,
    }
  end,
  nsmul := nsmul,
  nsmul_zero' := by {intro a, refl},
  nsmul_succ' := by {intros a x, refl},
  neg := neg,
  sub := sub,
  sub_eq_add_neg := begin
    intros a b,
    ext,
    {
      change a.re - b.re = (a.re + -b.re),
      ring,
    },{
      change a.im - b.im = (a.im + -b.im),
      ring,
    }
  end,
  zsmul := zsmul,
  zsmul_zero' := by {intro a, refl},
  zsmul_succ' := by {intros a b, refl},
  zsmul_neg' := by {intros a b, refl},
  add_left_neg := begin
    intro a, ext,
    {
      change -a.re + a.re = (0 : ℤ),
      ring,
    },{
      change -a.im + a.im = (0 : ℤ),
      ring,
    }
  end,
  add_comm := begin
    intros a b,
    ext,
    {
      change a.re + b.re = b.re + a.re,
      ring,
    },{
      change a.im + b.im = b.im + a.im,
      ring,
    }
  end,
  mul := prod,
  mul_assoc := begin
    intros a b c,
    ext,
    {
      change (a.re * b.re - a.im * b.im) * c.re - (a.re * b.im + a.im * b.re) * c.im = 
      a.re * (b.re * c.re - b.im * c.im) - a.im * (b.re * c.im + b.im * c.re),
      ring,
    },
    {
      change (a.re * b.re - a.im * b.im) * c.im + (a.re * b.im + a.im *b.re) * c.re = 
      a.re * (b.re * c.im + b.im * c.re) + a.im * (b.re * c.re - b.im * c.im),
      ring,
    }
  end,
  one := (1 : gaussian_ints),
  one_mul := begin
    intro a,
    ext,
    {
      change 1 * a.re - 0 * a.im = a.re,
      ring,
    },
    {
      change 1 * a.im + 0 * a.re = a.im,
      ring,
    }
  end,
  mul_one := begin
    intro a,
    ext,
    {change a.re * 1 - a.im * 0 = a.re, ring,},
    {change a.re * 0 + a.im * 1 = a.im, ring,}
  end,
  npow := npow,
  npow_zero' := by {intro a, refl},
  npow_succ' := by {intros a b, refl},
  left_distrib := begin
    intros a b c,
    ext,
    {
      change a.re * (b.re + c.re) - a.im * (b.im + c.im) = 
      (a.re * b.re - a.im * b.im) + (a.re * c.re - a.im * c.im),
      ring,
    },{
      change a.re * (b.im + c.im) + a.im * (b.re + c.re) =
      (a.re * b.im + a.im * b.re) + (a.re * c.im + a.im * c.re),
      ring,
    }
  end,
  right_distrib := begin
    intros a b c,
    ext,
    {
      change (a.re + b.re) * c.re - (a.im + b.im) * c.im =
      (a.re * c.re - a.im * c.im) + (b.re * c.re - b.im * c.im),
      ring,
    },
    {
      change (a.re + b.re) * c.im + (a.im + b.im) * c.re = 
      (a.re * c.im + a.im * c.re) + (b.re * c.im + b.im * c.re),
      ring,
    }
  end,
  mul_comm := begin
    intros a b,
    ext,
    {
      change a.re * b.re - a.im * b.im = b.re * a.re - b.im * a.im,
      ring,
    },
    {
      change a.re * b.im + a.im * b.re = b.re * a.im + b.im * a.re,
      ring,
    }
  end 
}

/--
Norm function for Gaussian integers. Defined by Re(x)^2 + Im(x)^2 rather than x * x.conj
-/
def norm (x : gaussian_ints) : ℤ := x.re ^ 2 + x.im ^ 2

lemma norm_nonneg : ∀ (x : gaussian_ints), 0 ≤ norm x :=
begin
  intro x,
  have hx := sq_nonneg x.re,
  have hy := sq_nonneg x.im,
  change 0 ≤ x.re^2 +x.im^2,
  linarith,
end
lemma sum_sqs_eq_zero  (x y : ℤ) : x^2 + y^2 = 0 → x = 0:=
begin
  intro h,
  have hx := sq_nonneg x,
  have hy := sq_nonneg y,
  apply @pow_eq_zero _ _ _ _ 2,
  linarith, apply_instance,
end
lemma norm_zero_iff_zero : ∀ (a : gaussian_ints), norm a = (0:ℤ) ↔ a = (0:gaussian_ints) :=
begin
  intro x,
  split,
  {
    intro h,
    change x.re^2 + x.im^2 = 0 at h,
    ext,
    {
      apply sum_sqs_eq_zero x.re x.im,
      exact h,
    },
    {
      rw add_comm at h,
      apply sum_sqs_eq_zero x.im x.re,
      exact h,
    }
  },{
    intro h,
    rw h,
    change (0 : ℤ) ^2 + (0 : ℤ)^2 = 0,
    norm_num,
  }
end

lemma norm_zero_eq_zero : norm 0 = 0 :=
begin
  change (0 : ℤ) ^2 + (0 : ℤ)^2 = 0,
  norm_num,
end

lemma norm_pos_if_nonzero {b : gaussian_ints} (h : b ≠ 0) : (0:ℤ) < norm b :=
begin
  change ¬(b = 0) at h,
  rw ←norm_zero_iff_zero at h,
  rw eq_comm at h,
  rw ←(ne.le_iff_lt h),
  exact norm_nonneg b,
end

lemma norm_mul (x y : gaussian_ints) : norm (x*y) = (norm x) * (norm y) :=
begin
  change (x.re * y.re - x.im * y.im)^2 + (x.re * y.im + x.im * y.re)^2 = (x.re^2+x.im^2) * (y.re^2 + y.im^2),
  ring,
end

lemma norm_div {x y: gaussian_ints} (h : x \ y) :  norm x ∣ norm y :=
begin
  cases h with k hk,
  use k.norm,
  rw ←norm_mul,
  rw hk,
end

lemma norm_conj_eq_norm (x : gaussian_ints) : norm(x) = norm(x.conj) :=
begin
  change norm x = x.re^2 + (-x.im)^2,
  rw neg_sq,
  refl,
end

lemma norm_eq_conj_mul (x : gaussian_ints) : coe (norm x) = x * x.conj :=
begin
  ext,
  change x.re^2 +x.im^2= x.re * x.re - x.im * (-x.im),
  ring,
  change 0 = x.re * (-x.im) + x.im * x.re,
  ring,
end

lemma norm_one_iff_unit {x : gaussian_ints}: norm x = 1 ↔ is_unit x :=
begin
  split,
  {
    intro h,
    rw is_unit_iff_exists_inv,
    apply_fun convert_int at h,
    change coe (norm x) = (1 : gaussian_ints) at h,
    rw norm_eq_conj_mul at h,
    use x.conj,
    exact h,
  },
  {
    intro h,
    rw is_unit_iff_exists_inv at h,
    cases h with i hi,
    apply_fun norm at hi,
    change (x * i).norm = 1^2 + 0^2 at hi,
    rw ( by ring :(1:ℤ)^2 + 0^2 = 1) at hi,
    rw norm_mul at hi,
    rw mul_comm at hi,
    exact int.eq_one_of_mul_eq_one_left (norm_nonneg x) hi,
  }
end

/-
The only units in ℤ[i] are 1, -1, i, -i.
-/
lemma all_the_units {x : gaussian_ints} : is_unit x ↔ x ∈ ({1, -1, ⟨0, 1⟩, ⟨0, -1⟩} : set gaussian_ints) :=
begin
  rw ←norm_one_iff_unit,
  split;
  intro h,
  {
    change x.re^2 +x.im^2 = 1 at h,
    have h2 : 0 ≤ (x.re^2), exact (sq_nonneg x.re), --doing what I did for h3 does not work with interval_cases???
    have h3 := sq_nonneg x.im,
    have h4 : x.re^2 ≤ 1,
    linarith,
    interval_cases (x.re^2) with h5,
    {
      rw h5 at h,
      rw zero_add at h,
      rw eq_comm at h5,
      rw (by ring: x.re^2 = x.re*x.re) at h5,
      rw zero_eq_mul at h5,
      rw or_self at h5,
      rw sqrt_one_eqn at h,
      cases h,
      right,right,left, ext, exact h5, exact h,
      right,right,right, ext, exact h5, exact h,
    },
    {
      rw h5 at h,
      nth_rewrite 1 ←add_zero (1:ℤ) at h,
      rw add_left_cancel_iff at h,
      rw eq_comm at h,
      rw (by ring: x.im^2 = x.im*x.im) at h,
      rw zero_eq_mul at h,
      rw or_self at h,
      rw sqrt_one_eqn at h5,
      cases h5,
      left, ext, exact h5, exact h,
      right, left, ext, exact h5, exact h,
    }
    
  },
  {
    cases h,
    rw h,
    change 1^2 + 0^2 = (1 : ℤ),
    norm_num,
    cases h,
    rw h,
    change (-1)^2 + 0^2 = (1 : ℤ),
    norm_num,
    cases h,
    rw h,
    change 0^2 + 1^2 = (1 : ℤ),
    norm_num,
    cases h,
    cases h,
    change 0^2 + (-1)^2 = (1 : ℤ),
    norm_num,
  }
end

lemma i_sq_minus_one : (⟨0, 1⟩: gaussian_ints)^2 = (⟨-1, 0⟩ : gaussian_ints) :=
begin
  rw (by ring: (⟨0, 1⟩:gaussian_ints)^2 = (⟨0, 1⟩ :gaussian_ints) * (⟨0, 1⟩ :gaussian_ints)),
  ext,
  norm_num [mul_re, mul_def, mul_im],
  norm_num [mul_re, mul_def, mul_im],
end

lemma i_cub_minus_i : (⟨0, 1⟩: gaussian_ints)^3 = (⟨0, -1⟩ : gaussian_ints) :=
begin
  rw (by ring: (⟨0, 1⟩:gaussian_ints)^3 = (⟨0, 1⟩ :gaussian_ints) * (⟨0, 1⟩ :gaussian_ints) * (⟨0, 1⟩ :gaussian_ints)),
  ext,
  norm_num [mul_re, mul_def, mul_im],
  norm_num [mul_re, mul_def, mul_im],
end

/-
The ring ℤ[i] is a Euclidean domain.
-/
instance : my_euclidean_domain gaussian_ints :=
{
  hzd := begin
    intros x y h,
    apply_fun norm at h,
    rw norm_mul at h,
    rw norm_zero_eq_zero at h,
    rw mul_eq_zero at h,
    rw norm_zero_iff_zero at h,
    rw norm_zero_iff_zero at h,
    exact h,
  end,
  norm := norm,
  norm_nonneg := norm_nonneg,
  norm_zero_iff_zero := norm_zero_iff_zero,
  hnorm := begin
    intros a b hb,
    let d_real := ((a * b.conj).re : ℚ)/((norm b) : ℚ),
    let d_imag := ((a * b.conj).im : ℚ)/((norm b) : ℚ),
    let d_real_rounded := round d_real,
    let d_imag_rounded := round d_imag,
    let q := gaussian_ints.mk d_real_rounded d_imag_rounded,
    use q,
    use a - b * q,
    split,
    {
      ring,
    },
    {
      have hre := abs_sub_round d_real,
      have him := abs_sub_round d_imag,
      have hre2 := sq_le_sq (le_abs_le hre),
      have him2 := sq_le_sq (le_abs_le him),
      rw (by norm_num : ((1:ℚ)/(2:ℚ))^2 = 1/4 ) at hre2 him2,
      change (a - b*q).re ^2 + (a - b*q).im^2 < norm b,
      have hdr : (d_imag - coe q.im) ^ 2 + (d_real - coe q.re) ^ 2 ≤ 1/2,
        linarith,
      have h3 : (0 : ℚ) < b.norm,
      {
        norm_cast,
        exact (norm_pos_if_nonzero hb),
      },
      have h4 : (b.norm : ℚ) ≠ 0, 
      {
        norm_cast,
        by_contra,
        apply hb,
        rw norm_zero_iff_zero b at h,
        exact h,
      },
      rw ←mul_le_mul_left h3 at hdr,
      have hlr : (b.norm : ℚ) * ((d_imag - ↑(q.im)) ^ 2 + (d_real - ↑(q.re)) ^ 2) = coe ((a - b * q).re ^ 2 + (a - b * q).im ^ 2),
      {
        push_cast,
        rw mul_add,
        have hsq_eval : ∀(a b : ℚ), (a - b)^2 = a^2 + b^2 - 2*a*b,
          intros a b,
          ring,
        rw hsq_eval d_imag (coe d_imag_rounded),
        rw hsq_eval d_real (coe d_real_rounded),
        rw mul_sub,
        rw mul_add,
        rw mul_sub,
        rw mul_add,
        rw (by ring : ↑(b.norm) * d_imag ^ 2 + ↑(b.norm) * ↑d_imag_rounded ^ 2 - ↑(b.norm) * (2 * d_imag * ↑d_imag_rounded) + (↑(b.norm) * d_real ^ 2 + ↑(b.norm) * ↑d_real_rounded ^ 2 - ↑(b.norm) * (2 * d_real * ↑d_real_rounded)) = 
        (↑(b.norm) * d_real ^ 2 +↑(b.norm) * d_imag ^ 2) - (↑(b.norm) * (2 * d_imag * ↑d_imag_rounded) + ↑(b.norm) * (2 * d_real * ↑d_real_rounded)) + ↑(b.norm) * ↑d_imag_rounded ^ 2  + ( ↑(b.norm) * ↑d_real_rounded ^ 2 )),
        have h_2d_b_mul : ↑(b.norm) * (2 * d_imag * ↑d_imag_rounded) + ↑(b.norm) * (2 * d_real * ↑d_real_rounded) = 2 * (a*b.conj).im * ↑d_imag_rounded + 2 * (a*b.conj).re * ↑d_real_rounded,
        {
          nth_rewrite 2 mul_comm,
          rw ←mul_assoc,
          rw ←mul_assoc,
          have hbim : (b.norm : ℚ) * (((a * b.conj).im : ℚ)/((norm b) : ℚ)) = ((a * b.conj).im : ℚ),
          {
            exact mul_div_cancel' ((a * b.conj).im : ℚ) h4,
          },
          have hdre : (b.norm : ℚ) * (((a * b.conj).re : ℚ)/((norm b) : ℚ)) = ((a * b.conj).re : ℚ),
          {
            exact mul_div_cancel' ((a * b.conj).re : ℚ) h4,
          },
          change ↑(b.norm) * (((a * b.conj).im : ℚ)/((norm b) : ℚ)) * 2 * ↑d_imag_rounded + ↑(b.norm) * (2 * d_real * ↑d_real_rounded) = 2 * ↑((a * b.conj).im) * ↑d_imag_rounded + 2 * ↑((a * b.conj).re) * ↑d_real_rounded,
          rw hbim,
          nth_rewrite 5 mul_comm,
          rw ←mul_assoc,
          rw ←mul_assoc,
          rw hdre,
          ring,
        },
        rw h_2d_b_mul,
        have hna_b_mul : ↑(b.norm) * d_real ^ 2 + ↑(b.norm) * d_imag ^ 2 = a.re ^2 + a.im ^2,
        {
          change ↑(b.norm) * (↑((a * b.conj).re) / ↑(b.norm)) ^ 2 + ↑(b.norm) * (↑((a * b.conj).im) / ↑(b.norm)) ^ 2 = 
          ↑(a.re) ^ 2 + ↑(a.im) ^ 2,
          rw mul_re,
          rw mul_im,
          change
          ↑(b.norm) * (↑(a.re * b.re - a.im * (-b.im)) / ↑(b.norm)) ^ 2 + 
          ↑(b.norm) * (↑(a.re * (-b.im) + a.im * b.re) / ↑(b.norm)) ^ 2 
          = ↑(a.re) ^ 2 + ↑(a.im) ^ 2,
          field_simp,
          norm_cast,
          change (b.re^2+b.im^2) * (a.re * b.re + a.im * b.im) ^ 2 + (b.re^2+b.im^2) * (-(a.re * b.im) + a.im * b.re) ^ 2 
          = (a.re ^ 2 + a.im ^ 2) * (b.re^2+b.im^2) ^ 2,
          ring,
        },
        rw hna_b_mul,
        norm_cast,
        change a.re ^ 2 + a.im ^ 2 - (2 * (a * b.conj).im * q.im + 
        2 * (a * b.conj).re * q.re) + (b.re^2 + b.im^2) * q.im ^ 2 + (b.re^2 + b.im^2) * q.re ^ 2 
        = (a.re - (b * q).re) ^ 2 + (a.im - (b * q).im) ^ 2,
        rw [mul_re, mul_re, mul_im, mul_im],
        change a.re ^ 2 + a.im ^ 2 - (2 * (a.re * (-b.im) + a.im * b.re) * q.im +
         2 * (a.re * b.re - a.im * (-b.im)) * q.re) + (b.re ^ 2 + b.im ^ 2) * q.im ^ 2 + (b.re ^ 2 + b.im ^ 2) * q.re ^ 2 =
         (a.re - (b.re * q.re - b.im * q.im)) ^ 2 + (a.im - (b.re * q.im + b.im * q.re)) ^ 2,
        ring,
      },
      suffices : ↑((a - b * q).re ^ 2 + (a - b * q).im ^ 2) < (b.norm : ℚ),
      exact int.cast_lt.mp this,
      rw ←hlr,
      linarith,
    },
    
  end 
}
/-
  Weaker separating powers trick to remove the unit multiplication since every unit has a cube root.
  We just do this by trying all the cases for units.
-/
theorem separating_powers_cubes {p a b : gaussian_ints} (hcop : coprime a b) (heq : p^3 = a * b) : ∃(r : gaussian_ints), r^3 = a :=
begin
  have h2 := separating_powers_trick hcop heq,
  cases h2 with r hr,
  cases hr with u hu,
  cases hu with hu hrn,
  rw all_the_units at hu,
  cases hu,
    use r,
    rw hu at hrn,
    rw one_mul at hrn,
    exact hrn,
  cases hu,
    use -r,
    rw hu at hrn,
    rw (by ring : (-1) * r ^ 3 = (-r)^3) at hrn,
    exact hrn,
  cases hu,
    use (-u) * r,
    rw (by ring: (-u * r)^3 = -(u^3) * r^3),
    rw hu at ⊢ hrn,
    rw i_cub_minus_i,
    rw (by ring : -(⟨0, -1⟩:gaussian_ints) = ⟨0, 1 ⟩ ),
    exact hrn,
  cases hu, cases hu,
    use ⟨0, 1⟩ * r,
    rw (by ring : ((⟨0, 1⟩:gaussian_ints) * r) ^ 3 = (⟨0, 1⟩:gaussian_ints)^3 * r^3),
    rw i_cub_minus_i,
    exact hrn,
end

end gaussian_ints



/-
The only solution to X^2 + 1 = Y^3 over Z is x = 0, y = 1
-/
theorem my_diophantine_equation (x y : ℤ) : x^2 + 1 = y^3 → x = 0 :=
begin
  intro he,
  have heven : even x,
  {
    by_contra,
    rw ←int.odd_iff_not_even at h,
    cases h with u hu,
    apply_fun (λ t, t % 4) at he,
    rw hu at he,
    rw (by ring: (2*u + 1)^2 + 1 = 2 + (u^2 + u) * 4) at he,
    rw int.add_mul_mod_self at he,
    rw (by norm_num: (2 : ℤ ) % 4 = 2) at he,
    by_cases even y,
    {
      cases h with v hv,
      have h2 := int.mod_lt_of_pos v (by norm_num : (0:ℤ) < 4),
      have h3 := int.mod_nonneg v (by norm_num : 4 ≠ (0:ℤ)),
      rw hv at he,
      rw (by ring: (2 * v) ^ 3 =  ( 2*v^3) * 4) at he,
      rw int.mul_mod_left at he,
      linarith,
    },
    {
      rw ←int.odd_iff_not_even at h,
      cases h with v hv,
      rw hv at he,
      rw (by ring: ((2:ℤ) * v + 1)^3 = (6*v + 1) + ( (2*v^3 + 3 * v^2) * 4) ) at he,
      rw int.add_mul_mod_self at he,
      have h2 := int.mod_lt_of_pos v (by norm_num : (0:ℤ) < 4),
      have h3 := int.mod_nonneg v (by norm_num : 4 ≠ (0:ℤ)),
      rw int.add_mod at he,
      rw int.mul_mod at he,
      interval_cases (v % 4);
      rw h at he,
        rw (by norm_num : (6 % 4 * 0 % 4 + 1 % 4) % 4 = (1:ℤ )) at he,
        linarith,
        rw (by norm_num : (6 % 4 * 1 % 4 + 1 % 4) % 4 = (3:ℤ )) at he,
        linarith,
        rw (by norm_num : (6 % 4 * 2 % 4 + 1 % 4) % 4 = (1:ℤ )) at he,
        linarith,
        rw (by norm_num : (6 % 4 * 3 % 4 + 1 % 4) % 4 = (3:ℤ )) at he,
        linarith,
    },
  },
  have haqodd : odd (x^2 + 1),
  {
    cases heven with k hk,
    rw hk,
    rw (by ring: (2 * k) ^ 2 + 1 = 2 * (2* k^2) + 1),
    use 2 * k^2,
  },
  have h2 : (x : gaussian_ints) ^ 2 + (1:gaussian_ints) = (y:gaussian_ints) ^ 3,
  {
    rw (by ring : (x : gaussian_ints)^2 = coe x * coe x),
    rw ←gaussian_ints.coe_mul,
    rw (by ring : (y : gaussian_ints)^3 = coe y * coe y * coe y),
    rw ←gaussian_ints.coe_mul,
    rw ←gaussian_ints.coe_mul,
    change coe (x * x + 1)   = coe (y * y * y),
    rw (by ring : x*x = x^2 ),
    rw he,
    rw (by ring : y*y*y = y^3 ),
  },
  let a := (x : gaussian_ints),
  let b := (y : gaussian_ints),
  let i := gaussian_ints.mk 0 1,
  let q := gaussian_ints.mk x 1,
  have hq : q = a + i,
  {
    ext,
    change x = x + 0,
    rw add_zero,
    change (1 : ℤ) = 0 + 1,
    norm_num,
  },
  rw (by ring : a^2 + 1 = (a + i) * (a - i)) at h2,
  have hcop : coprime (a + i) (a - i),
  {
    intros z h h2,
    have h3 := divis_sub h h2,
    rw (by ring: a + i - (a - i) = 2 * i) at h3,
    have h4 := gaussian_ints.norm_div h3,
    have h5 := gaussian_ints.norm_div h,
    change z.norm ∣ 0^2 + 2^2 at h4,
    rw (by norm_num: (0:ℤ) ^ 2 + 2 ^ 2 = 4) at h4,
    have hd := int.le_of_dvd  (by norm_num) h4,
    rw ←hq at h5,
    change z.norm ∣ (x^2 + 1^2) at h5,
    rw (by norm_num: (1:ℤ)^2 = 1) at h5,
    have h6 := int.odd_div h5 haqodd,
    have h7 := gaussian_ints.norm_nonneg z,
    rw ←gaussian_ints.norm_one_iff_unit,
    rw int.odd_iff_not_even at h6,
    interval_cases z.norm,
      exfalso, apply h6, use 0, rw mul_zero, exact h_1,
      exact h_1,
      exfalso, apply h6, use 1, rw mul_one, exact h_1,
      exfalso, rw h_1 at h4, apply (by norm_num : ¬((3:ℤ) ∣ 4)), exact h4,
      exfalso, apply h6, use 2, rw h_1, norm_num,
  },
  
  rw eq_comm at h2,
  have hpow := gaussian_ints.separating_powers_cubes hcop h2,
  cases hpow with r hr,
  rw ←hq at hr,
  rw gaussian_ints.ext_eq at hr,
  change (r ^ 3).re = x ∧ (r ^ 3).im = 1 at hr,
  cases hr with hrr hri,
  rw (by ring_nf : (r^3).re = (r*r*r).re) at hrr,
  rw (by ring_nf : (r^3).im = (r*r*r).im) at hri,
  rw gaussian_ints.mul_re at hrr,
  rw gaussian_ints.mul_re at hrr,
  rw gaussian_ints.mul_im at hrr,
  rw gaussian_ints.mul_im at hri,
  rw gaussian_ints.mul_im at hri,
  rw gaussian_ints.mul_re at hri,
  rw (by ring : (r.re * r.re - r.im * r.im) * r.re - (r.re * r.im + r.im * r.re) * r.im = r.re^3 - 3 * r.re * r.im^2) at hrr,
  rw (by ring: (r.re * r.re - r.im * r.im) * r.im + (r.re * r.im + r.im * r.re) * r.re = r.im * (3 * r.re^2 - r.im^2) ) at hri,
  rw mul_comm at hri,
  by_cases hrip : 0 ≤ r.im,
  {
    have h3 := int.eq_one_of_mul_eq_one_left hrip hri,
    rw [h3, mul_one] at hri,
    apply_fun (λt, t+1) at hri,
    rw (by ring: 1 + (1: ℤ ) = 2) at hri,
    rw sub_eq_add_neg at hri,
    rw add_assoc at hri,
    rw (by ring: -1 ^ 2 + 1 = (0:ℤ)) at hri,
    rw add_zero at hri,
    have h4 : (3:ℤ) ∣ 2,
    {
      use r.re^2,
      rw hri,
    },
    exfalso,
    apply (by norm_num : ¬ ((3:ℤ) ∣ 2)), 
    exact h4,
  },
  {
    have hrip2 : 0 ≤ -r.im,
    linarith [hrip],
    rw (by ring: (3 * r.re ^ 2 - r.im ^ 2) * r.im = (-(3 * r.re ^ 2 - r.im ^ 2)) * (-r.im)) at hri,
    have h3 := int.eq_one_of_mul_eq_one_left hrip2 hri,
    rw [h3,mul_one] at hri,
    rw [eq_comm, eq_neg_iff_eq_neg] at h3,
    rw h3 at hri,
    rw [eq_comm, eq_neg_iff_eq_neg] at hri,
    apply_fun (λt, t+1) at hri,
    rw (by ring: -1 + (1: ℤ ) = 0) at hri,
    rw sub_eq_add_neg at hri,
    rw add_assoc at hri,
    rw (by ring: -(-1) ^ 2 + 1 = (0:ℤ)) at hri,
    rw add_zero at hri,
    rw eq_comm at hri,
    rw zero_eq_mul at hri,
    cases hri,
      linarith [hri],
    rw eq_comm at hri,
    rw (by ring: r.re^2 = r.re * r.re) at hri,
    rw zero_eq_mul at hri,
    rw or_self at hri,
    rw ←hrr,
    rw [hri, h3],
    norm_num,
  }
end

#lint