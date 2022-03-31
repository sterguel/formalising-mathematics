import cw2_restructured

/-
  This is part of coursework 3!
-/
open myring

/-
Two elements of a ring are coprime if only units divide them both.
-/
def coprime {R : Type} [comm_ring R] (a b : R) : Prop := ∀ (d : R), d \ a → d \ b → is_unit d

lemma divis_add {R : Type} [comm_ring R] {a b c: R} : a \ b → a \ c → a \ (b+c) :=
begin
  intros h1 h2,
  cases h1 with kb hkb,
  cases h2 with kc hkc,
  use (kb + kc),
  rw mul_add,
  rw [hkb, hkc],
end

lemma divis_neg  {R : Type} [comm_ring R] {a b : R} : a \ b → a \ (-b) :=
begin
  intro h,
  cases h with k hk,
  use -k,
  rw hk,
  ring,
end 

lemma divis_sub {R : Type} [comm_ring R] {a b c: R} : a \ b → a \ c → a \ (b-c) :=
begin
  intros h1 h2,
  cases h1 with kb hkb,
  cases h2 with kc hkc,
  use (kb - kc),
  rw mul_sub,
  rw [hkc, hkb],
end

/-
Bezout's identity for PIDs
I thought this might have been useful but it turns out it's not.
I'm leaving it in because it might be interesting
-/
theorem bezout_identity {R: Type} [pid R] {a b : R} (h : coprime a b) : ∃(c d : R), a*c + b*d = 1 :=
begin
  let I := sum_ideal (principal_ideal a) (principal_ideal b),
  have hi := pid.hpid I,
  cases hi with d hd,
  have hai : a ∈ I,
  {
    use a,
    split,
      use 1,
      rw mul_one,
      use 0,
      split, 
        exact zero_mem_ideal,
        rw add_zero,
  },
  have hbi : b ∈ I,
  {
    use 0,
    split,
      exact zero_mem_ideal,
      use b,
      split,
        use 1,
        rw mul_one,
        rw zero_add,
  },
  have had : d \ a,
  {
    rw hd at hai,
    cases hai with e he,
    use e,
    exact he,
  },
  have hbd : d \ b,
  {
    rw hd at hbi,
    cases hbi with e he,
    use e,
    exact he,
  },
  have hone : (1:R) ∈ I,
  {
    rw hd,
    have hu := h d had hbd,
    rw is_unit_iff_exists_inv at hu,
    cases hu with di hdi,
    use di,
    exact eq_comm.mp hdi,
  },
  cases hone with k hk,
  cases hk with hk hl,
  cases hl with l hl,
  cases hl with hl hkl,
  cases hk with q hq,
  cases hl with r hr,
  rw hkl,
  use q,
  use r,
  rw hq,
  rw hr,
end

/-
Euclid's Lemma for PIDs.
I thought this might have been useful but it turns out it's not.
I'm leaving it in because it might be interesting
-/
theorem euclid_lemma {R : Type} [pid R] (n a b : R) (hc : coprime n a) : n \ (a*b) → n \ b :=
begin
  intro h,
  have h2 := bezout_identity hc,
  cases h2 with r hr,
  cases hr with s hs,
  apply_fun λ x, b*x at hs,
  rw mul_add at hs,
  rw mul_one at hs,
  cases h with d hd,
  use b*r + s*d,
  nth_rewrite 0 ←hs,
  nth_rewrite 1 ←mul_assoc,
  nth_rewrite 3 mul_comm,
  rw hd,
  ring,
end

variables {R : Type} [ufd R] 

lemma associates_equiv : equivalence (@associates R _ ) :=
begin
  split,
  {
    intro x,
    use 1,
    split,
    exact is_unit_one,
    rw mul_one,
  },
  split,
  {
    intros x y h,
    cases h with u hu,
    cases hu with hui hu,
    rw hu,
    rw is_unit_iff_exists_inv at hui,
    cases hui with ui hui,
    use ui,
    split,
    {
      rw is_unit_iff_exists_inv,
      use u,
      rw mul_comm,
      exact hui,
    },
    {
      rw [mul_assoc, hui, mul_one],
    }
  },
  {
    intros x y z h1 h2,
    cases h1 with u1 hu1,
    cases h2 with u2 hu2,
    cases hu1 with hui1 hu1,
    cases hu2 with hui2 hu2,
    use (u1 * u2),
    split,
    {
      exact is_unit.mul hui1 hui2,
    },
    {
      rw [hu2, hu1, mul_assoc],
    }
  }
end 


/-
def S (R: Type) [ufd R] : setoid R :=
{ r := associates,
  iseqv := associates_equiv }

-- I'm not sure how to get this one working
def irreducible_Ra : quotient (S R) → Prop := quotient.lift (λ a, irreducible a) begin
  sorry
end

theorem ufd_finite_factorisation  (a : quotient (S R)) :
 ∃ (s : multiset (quotient (S R))), ∀(x ∈ s), irreducible (coe x) :=
begin
  sorry
end
-/

/-
The separating powers trick for UFDs

Not enough time to do this :(
-/
theorem separating_powers_trick {R : Type} [ufd R] {p a b : R} {n : ℕ} (hcop : coprime a b) (heq : p^n = a * b) : 
∃ (r u : R), is_unit u  ∧ u * r^n =  a := 
begin
  sorry
end