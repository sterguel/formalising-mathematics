/-
This definition of UFD is quite clunky! I will instead use the one in the groups + rings notes in Thm 5.12
to avoid having to deal with factorisations.

structure factorisation (r : R) :=
(els : finset R)
(no_units : ∀ (t : R), t ∈ els → ¬is_unit t)
(irreducible : ∀ (t : R), t ∈ els → irreducible t)
(prod_r : finset.prod els (λ x, x) = r)


def facts_equiv {r : R} (a b : factorisation r) : Prop :=
  ∀(t : R), t ∈ a.els ↔ ∃ (c d: R), is_unit c ∧ d ∈ b.els ∧ c * d = t



def is_ufd  (R : Type) [comm_ring R] [is_integral_domain R] : Prop :=
  ∀(r : R), ¬(is_unit r) → ∃ (f : factorisation r), ∀ (g : factorisation r), facts_equiv f g


lemma irreducible_is_prime_ufd {b a p : R} (hint : is_integral_domain R) (hufd : @is_ufd R _ hint): irreducible p → (p \ (a*b)) →  p \ a ∨ p \ b:=
begin
  intro hirr,
  intro hdiv,
  by_cases ha :(is_unit a) ,
    rw is_unit_iff_exists_inv at ha,
    right,
    cases ha with ainv hainv,
    cases hdiv,
    use (hdiv_w * ainv),
    apply_fun (λ x, ainv * x) at hdiv_h,
    rw ←mul_assoc at hdiv_h, rw mul_comm at hainv,
    rw hainv at hdiv_h, rw one_mul at hdiv_h,
    rw ←mul_assoc, rw mul_comm, exact hdiv_h,
  by_cases hb : is_unit b,
    rw is_unit_iff_exists_inv at hb,
    left,
    cases hb with binv hbinv,
    cases hdiv,
    use (hdiv_w * binv),
    apply_fun (λ x, binv * x) at hdiv_h,
    rw mul_comm at hdiv_h,
    rw mul_assoc at hdiv_h,
    rw hbinv at hdiv_h,
    rw mul_one at hdiv_h, rw ← mul_assoc,
    rw mul_comm, exact hdiv_h,
    by_contra,
end

-/