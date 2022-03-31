import cw3.cw2_restructured
import cw3.utils
-- Euclidean domain stuff for CW3
-- Definition and also a proof that every Euclidean domain is a PID.
-- This takes ages to compile for some reason

/--
A Euclidean domain is an integral domain with a nonnegative norm function and Euclidean division (with this norm).
-/
class my_euclidean_domain (E: Type) extends integral_domain E :=
(norm : E → ℤ )
(norm_nonneg: ∀(a : E), 0 ≤ norm a )
(norm_zero_iff_zero : ∀ (a : E), norm a = 0 ↔ a = 0) 
-- ^not necessary but you can always come up with such a norm and we would complicate hnorm further
(hnorm : ∀ (a b : E), b ≠ 0 → ∃ (q r : E), a = b * q + r ∧ norm(r) < norm(b))

namespace my_euclidean_domain
@[priority 100]
instance (E: Type) [my_euclidean_domain E]: pid E :=
{
  hpid :=
  begin
    intro I,
    by_cases ∃ (i : E),  i ≠ 0 ∧ i ∈ I,
    {
      let S := {i : E | i ≠ 0 ∧ i ∈ I.iset},
      have hn : set.nonempty S,{
        rw set.nonempty_def,
        cases h,
        use h_w,
        exact h_h,
      },
      let T := {n : ℤ | ∃ (x ∈ S), norm x = n},
      have htn : T.nonempty,
      {
        cases hn with s hs,
        use (norm s),
        use s,
        split, exact hs, refl,
      },
      have htb : bdd_below T,
      {
        use 0,
        intros x h2,
        cases h2 with a ha,
        cases ha with ha ha2,
        rw ←ha2,
        apply norm_nonneg,
      },
      have htm := bdd_below_Z_set_has_minimum htn htb,
      cases htm with M hM,
      cases hM with hM hM2,
      cases hM with a ha,
      use a,
      cases ha with has ha,
      ext,
      split,
      {
        intro h,
        have h2 := @hnorm E _ ,
        specialize h2 x a,
        have h3 := h2 has.left,
        cases h3 with q h3,
        cases h3 with r hr,
        use q,
        cases hr with hre hrm,
        rw hre,
        nth_rewrite 1 ←add_zero (a*q),
        suffices : r = 0,
        rw this,
        have hr : r = x + -(a*q),
        rw hre,
        rw add_comm,
        rw ←add_assoc,
        rw add_left_neg,
        rw zero_add,
        have hri : r ∈ I,
        rw hr,
        apply I.add_mem,
        exact h,
        apply I.neg_mem,
        rw mul_comm,
        apply I.r_mul_mem,
        exact has.right,
        by_contra rnz,
        change r ≠ 0 at rnz,
        have hrs : r ∈ S,
        {
          split,
          exact rnz,
          exact hri,
        },
        have har : norm a ≤ norm r,
        {
          rw ha,
          specialize hM2 (norm r),
          apply hM2,
          use r,
          split, exact hrs, refl,
        },
        rw ←not_lt at har,
        apply har,
        exact hrm,
      },
      {
        intro h,
        cases h with u hu,
        rw hu,
        rw mul_comm,
        apply I.r_mul_mem,
        exact has.right,
      }
    },
    {
      rw not_exists at h,
      use 0,
      ext,
      split,
      {
        intro h2,
        specialize h x,
        rw and_comm at h,
        rw not_and at h,
        have h3 := not_not.mp (h h2),
        rw h3,
        use 0,
        rw mul_zero,
      },
      {
        intro h2,
        cases h2 with q hq,
        rw zero_mul at hq,
        rw hq,
        change (0:E) ∈ I,
        exact zero_mem_ideal,
      }
    }
  end
}
end my_euclidean_domain

#lint