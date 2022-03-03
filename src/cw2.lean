import tactic
import data.set.basic


/--
An ideal of R consists of a nonempty subset of R which is closed under addition, additive inverses, 
and multiplication by elements of R.
-/
@[nolint has_inhabited_instance]
structure myideal (R : Type) [comm_ring R] :=
  (iset : set R)
  (not_empty : iset.nonempty)
  (r_mul_mem' {x r}: x ∈ iset → r * x ∈ iset)
  (add_mem' {x y} : x ∈ iset → y ∈ iset → (x + y) ∈ iset)
  (neg_mem' {x} : x ∈ iset → -x ∈ iset)
  
attribute [ext] myideal

namespace myideal

variables {R : Type} [comm_ring R] (I : myideal R)
instance : has_mem R (myideal R) :=
{ mem := λ x i , x ∈ i.iset}

instance : has_coe (myideal R) (set R) := 
{coe := λ x, x.iset}

instance : has_subset (myideal R) :=
{ subset := λ x y, x.iset ⊆ y.iset }

theorem add_mem {x y : R}: x ∈ I → y ∈ I → x + y ∈ I := by apply add_mem'

theorem neg_mem {x : R} : x ∈ I → -x ∈ I := by apply neg_mem'

theorem r_mul_mem {x r : R} : x ∈ I → r * x ∈ I := by apply r_mul_mem'
end myideal


variables {R : Type} [comm_ring R]

/--
An integral domain has no zero divisors.
-/
def is_integral_domain (R: Type) [comm_ring R]: Prop :=
  ∀ (x y : R), x * y = 0 → x = 0 ∨ y = 0

/--
A principal ideal is of the form aR for some a ∈ R
-/
def principal_ideal (x : R) : myideal R :=
{ 
  iset := { i : R | ∃(v:R), i = x * v},
  not_empty := begin
    rw set.nonempty_def,
    use x,
    use 1,
    rw mul_one,
  end,
  r_mul_mem' := begin
    intro i,
    intro j,
    intro h,
    cases h,
    use (j * h_w),
    rw h_h,
    ring,
  end,
  add_mem' := begin
    intros i j hi hj,
    cases hi,
    cases hj,
    use hi_w + hj_w,
    rw mul_add,
    rw hi_h, rw hj_h,
  end,
  neg_mem' := begin
    intros i hi,
    cases hi,
    use -hi_w,
    rw hi_h,
    ring,
  end 
}
/--
An integral domain is a PID iff every ideal is principal.
-/
def is_pid (R: Type) [comm_ring R]: Prop :=
  is_integral_domain R ∧ ∀(I : myideal R), ∃ (x : R), I = principal_ideal x


--1 ∈ I → I = R
lemma one_mem_ideal_R {I : myideal R} : (1:R) ∈ I → coe I = {x : R | true} :=
begin
  intro h,
  ext,
  split,
  intro, triv,
  intro h2,
  rw ←mul_one x,
  apply myideal.r_mul_mem, 
  exact h,
end

lemma zero_mem_ideal {I : myideal R} : (0:R) ∈ I :=
begin
  have h := myideal.not_empty I,
  rw set.nonempty at h,
  cases h with x hx,
  have h2 : x + (-x) = 0,
  ring,
  rw ←h2,
  apply myideal.add_mem I,
  exact hx,
  apply myideal.neg_mem I,
  exact hx,
end

/--
The sum of two ideals is also an ideal.
-/
def sum_ideal (I J : myideal R) : myideal R :=
{ iset := {r : R | ∃ (i ∈ I) (j ∈ J), r = i + j},
  not_empty := begin
    have h1 := myideal.not_empty I,
    have h2 := myideal.not_empty J,
    rw set.nonempty at h1 h2 ⊢,
    cases h1,
    cases h2,
    use h1_w + h2_w,
    use h1_w, split, exact h1_h,
    use h2_w, split, exact h2_h,
    refl,
  end,
  r_mul_mem' := begin
    intros x r h,
    cases h with i h2,
    cases h2 with hi h2,
    cases h2 with j h2,
    cases h2 with hj h2,
    rw h2,
    rw mul_add,
    use r * i,
    split,
      apply myideal.r_mul_mem,
      exact hi,
    use r * j,
    split,
      apply myideal.r_mul_mem,
      exact hj,
    refl,
  end,
  add_mem' := begin
    intros x y hxm hym,
    cases hxm with xi hxi,
    cases hxi with hxi h2,
    cases h2 with xj hxj,
    cases hxj with hxj hx,
    cases hym with yi hyi,
    cases hyi with hyi h2,
    cases h2 with yj hyj,
    cases hyj with hyj hy,
    use xi + yi,
    split,
    apply myideal.add_mem, exact hxi, exact hyi,
    use xj + yj,
    split,
    apply myideal.add_mem, exact hxj, exact hyj,
    rw hy,
    rw hx,
    ring,
  end,
  neg_mem' := begin
    intros x h,
    cases h with i hi,
    cases hi with hi h2,
    cases h2 with j h2,
    cases h2 with hj h2,
    use -i,
    split,
    apply myideal.neg_mem,
    exact hi,
    use -j,
    split,
    apply myideal.neg_mem,
    exact hj,
    rw h2, ring,
  end 
}

notation I ` + ` J := sum_ideal I J

/--
An element r of R is irreducible iff it is not a unit and 
for all factorisations x * y = r, x or y is a unit.
-/
def irreducible (r : R) : Prop :=
  ¬is_unit r ∧ ∀(x y : R), x * y = r → is_unit x ∨ is_unit y

lemma r_prod_unit_r_unit (r a : R) (hpu : is_unit (r * a)) :
  is_unit r :=
begin
  have h2:=  is_unit.exists_right_inv hpu,
  cases h2,
  rw is_unit_iff_exists_inv',
  use a * h2_w, rw mul_comm, rw ← mul_assoc, exact h2_h,
end

lemma unit_mul_irr_is_irr (r a : R) (hirr :irreducible r) (hu: is_unit a) :
 irreducible (a * r) :=
begin
  split,
  {
    by_contra,
    cases hirr, 
    apply hirr_left, 
    apply r_prod_unit_r_unit r a, 
    rw mul_comm, 
    exact h
  },
  {
    intros x y h,
    have h2 : ∃ (b : R), r = (b * x) * y,
      rw is_unit_iff_exists_inv at hu,
      cases hu with c h3,
      use c, rw mul_assoc, rw h,
      ring_nf, rw mul_assoc, rw h3, rw mul_one,
    cases hirr,
    cases h2 with b hb,
    specialize hirr_right (b * x) y,
    rw eq_comm at hb,
    have h3 := hirr_right hb,
    cases h3,
    left, 
      rw mul_comm at h3, 
      apply r_prod_unit_r_unit x b, 
      exact h3,
    right,
    exact h3,
  }
end

/--
  For some a and b, a divides b iff there is a c ∈ R such that a * c = b
-/
def divisible (a b: R) : Prop :=
  ∃ (c : R), b = a * c

notation a ` \ ` b := divisible a b

/--
  Two elements a b are associates iff a = b * c for some unit c.
-/
def associates (a b : R) : Prop :=
  ∃ (c : R), is_unit c ∧ b = a * c

notation a ` ~ ` b := associates a b

lemma assoc_sym (a b : R) : a ~ b → b ~ a:=
begin
  intro h,
  cases h with u h2,
  cases h2 with hunit h3,
  rw is_unit_iff_exists_inv at hunit,
  cases hunit with uinv huinv,
  use uinv,
  split,
    rw is_unit_iff_exists_inv,
    use u,
    rw mul_comm, 
    exact huinv,
  rw h3,
  rw mul_assoc,
  rw huinv,
  rw mul_one,
end

lemma symm_divisible_associates_int_domain (hint : is_integral_domain R) (a b : R) : a \ b → b \ a → a ~ b :=
begin
  intros h1 h2,
  cases h1 with x hx,
  cases h2 with y hy,
  by_cases a ≠ 0,
  {
    rw hx at hy,
    apply_fun λ x, x + (-a) at hy,
    rw add_neg_self at hy,
    rw ←mul_one (-a) at hy,
    rw neg_mul_comm a 1 at hy,
    rw mul_assoc at hy,
    rw ←mul_add at hy,
    specialize hint a (x * y + (-1)),
    have h2 := hint (eq.symm hy),
    cases h2,
    exfalso, apply h, exact h2,
    apply_fun λ x, x + 1 at h2,
    rw zero_add at h2,
    rw add_assoc at h2,
    rw neg_add_self at h2,
    rw add_zero at h2,
    use x,
    split,
    rw is_unit_iff_exists_inv,
    use y, 
    exact h2,
    exact hx,
  },
  {
    use 1,
    split,
    exact is_unit_one,
    rw not_ne_iff at h,
    rw h at hx,
    rw hx,
    rw h,
    rw zero_mul,
    rw zero_mul,
  }
end

lemma generators_associate_if_ideals_eq (a b : R) (hint : is_integral_domain R):
  principal_ideal a = principal_ideal b → a ~ b :=
begin
  intro h,
  have h1 : a ∈ principal_ideal a,
    use 1, rw mul_one,
  have h2 : b ∈ principal_ideal b,
    use 1, rw mul_one,
  rw h at h1,
  rw ←h at h2,
  apply symm_divisible_associates_int_domain,
  exact hint,
  exact h2,
  exact h1,
end

/--
In a dividing sequence, each term is divisible by the next term.
-/
def dividing_sequence (f : ℕ → R) : Prop :=
∀ (n : ℕ),  f (n + 1) \ f n

/--
A unique factorisation domain (UFD) is an integral domain such that:
  All infinite dividing sequences 'stabilise': past some n ∈ ℕ, all terms are associate.#check
  All irreducible elements are prime.
-/
def is_ufd  (R : Type) [comm_ring R] : Prop :=
  is_integral_domain R ∧ (∀(f : ℕ → R), dividing_sequence f → 
  ∃ (m : ℕ), ∀(q : ℕ), m ≤ q → f q ~ f (q + 1) ) ∧
   (∀ (p: R), irreducible p →∀ (a b: R), p \ (a*b) → p \ a ∨ p \ b )

/--
In an ascending ideal chain, each ideal is contained in the next one.
-/
def asc_ideal_chain (i : ℕ → myideal R) : Prop :=
  ∀ (n : ℕ), i n ⊆ i (n + 1) 

lemma asc_ideal_chain_add (i : ℕ → myideal R) :
asc_ideal_chain i → ∀(n : ℕ), ∀ (m : ℕ),  i n ⊆  i (m+n) :=
begin
  intros h n m,
  induction m,
  rw zero_add, refl,
  specialize h (m_n + n),
  rw nat.succ_eq_add_one,
  
  change (i n).iset ⊆ (i (m_n + n)).iset at m_ih,
  change (i (m_n + n)).iset ⊆ (i (m_n + n + 1)).iset at h,
  change (i n).iset ⊆ (i (m_n + 1 + n)).iset,
  apply set.subset.trans,
  exact m_ih,
  nth_rewrite_rhs 1 add_comm,
  rw add_assoc,
  nth_rewrite_rhs 0 add_comm,
  exact h,
end

lemma asc_ideal_chain_ind (i : ℕ → myideal R) :
asc_ideal_chain i ↔ ∀(n : ℕ), ∀ (m : ℕ),  n ≤ m → i n ⊆ i m :=
begin
  split,
  {
    intros h n m h2,
    have h3 : ∃ (r: ℕ), n + r = m,
      use m - n,
      linarith,
    cases h3 with s hs,
    rw ←hs,
    rw add_comm,
    apply asc_ideal_chain_add,
    exact h,
  },
  {
    intros h n,
    specialize h n (n+1),
    apply h,
    norm_num,
  }
end

theorem pid_is_noetherian (R : Type) [comm_ring R] (hpid : is_pid R) 
(i :ℕ →  myideal R) (hinc : asc_ideal_chain i)  : 
∃(r : ℕ), ∀(s : ℕ ), r ≤ s → i s = i (s + 1)
 :=
begin
  cases hpid with hint hpid,
  let S := set.Union (λ (x : ℕ), myideal.iset (i x)),
  let si := myideal.mk S,
  let sii : myideal R,
  apply si,
  {
    rw set.nonempty, 
    let i0 := i 0,
    have hne := myideal.not_empty i0,
    rw set.nonempty at hne,
    cases hne with x0 hx0,
    use x0,
    rw set.mem_Union,
    use 0, exact hx0,
  },
  {
    intros x r h,
    rw set.mem_Union at h ⊢,
    cases h,
    use h_w,
    apply myideal.r_mul_mem',
    exact h_h,
  },{
    intros x y h1 h2,
    rw set.mem_Union at h1 h2 ⊢,
    cases h1 with i1 hi1,
    cases h2 with i2 hi2,
    by_cases i1 ≤ i2,
    {
      have h3 := ((asc_ideal_chain_ind i).mp) hinc,
      specialize h3 i1 i2,
      have h4 := h3 h,
      use i2,
      apply myideal.add_mem',
      apply set.mem_of_subset_of_mem h4,
      exact hi1,
      exact hi2,
    },
    {
      have hbt : i2 ≤ i1,
        rw le_iff_lt_or_eq,
        left,
        push_neg at h,
        exact h,
      have h3 := ((asc_ideal_chain_ind i).mp) hinc,
      specialize h3 i2 i1,
      have h4 := h3 hbt,
      use i1,
      apply myideal.add_mem',
      exact hi1,
      apply set.mem_of_subset_of_mem h4,
      exact hi2,
    } 
  },{
    intros x h,
    rw set.mem_Union at h ⊢,
    cases h with b hb,
    use b,
    apply myideal.neg_mem',
    exact hb,
  },
  specialize hpid sii,
  cases hpid with a ha,
  have hasi : a ∈ sii,
    rw ha,
    change ∃(v:R), a = a * v,
    use 1,
    rw mul_one,
  change a ∈ sii.iset at hasi,
  rw set.mem_Union at hasi,
  cases hasi with q hq,
  use q,
  intro s,
  intro hsq,
  have hisq : (i q).iset = S,
  {
    ext,
    split,
      intro h,
      rw set.mem_Union,
      use q, exact h,
    intro h,
    change x ∈ sii.iset at h,
    rw ha at h,
    cases h,
    rw mul_comm at h_h,
    rw h_h,
    apply myideal.r_mul_mem',
    exact hq,
  },
  apply myideal.ext,
  apply set.subset.antisymm,
  specialize hinc s,
  exact hinc,
  apply @set.subset.trans _ (i (s + 1)).iset (i q).iset,
  rw hisq,
  exact set.subset_Union (λ (x : ℕ), myideal.iset (i x)) (s + 1),
  rw asc_ideal_chain_ind at hinc,
  specialize hinc q s,
  apply hinc,
  exact hsq,
end

theorem pid_irreducible_is_prime (hpid : is_pid R)  (p : R) (hirr : irreducible p) :
  ∀ (a b : R), p \ (a * b) → p \ a ∨  p \ b :=
begin
  cases hpid with hint hpid,
  intros a b h,
  let I := sum_ideal (principal_ideal a) (principal_ideal p),
  specialize hpid I,
  cases hpid with d hd,
  have hpi: p ∈ I,
    use 0,
    split,
    exact zero_mem_ideal,
    use p,
    split,
    use 1,
    rw mul_one,
    rw zero_add,
  rw hd at hpi,
  cases hpi with r hdr,
  cases hirr,
  specialize hirr_right d r,
  have hut := hirr_right (eq_comm.mpr hdr),
  cases hut,
  { 
    right,
    have hone : (1:R) ∈ I,
      rw is_unit_iff_exists_inv at hut,
      rw hd,
      cases hut with di hdi,
      use di,
      rw hdi,
    cases hone with u h2,
    cases h2 with hu h2,
    cases h2 with v h2,
    cases h2 with hv h2,
    cases hu with s hs,
    cases hv with t ht,
    rw hs at h2,
    rw ht at h2,
    apply_fun λ x, b*x at h2,
    rw mul_one at h2,
    rw mul_add at h2,
    rw h2,
    rw ← mul_assoc,
    rw mul_comm b a,
    cases h with q hq,
    rw hq,
    use q * s + b * t,
    ring,
  },{
    have hai : a ∈ I,
      use a,
      split,
      use 1,
      rw mul_one,
      use 0,
      split,
      exact zero_mem_ideal,
      rw add_zero,
    rw hd at hai,
    cases hai with e he,
    rw is_unit_iff_exists_inv at hut,
    cases hut with ri hri,
    apply_fun λ x, x * ri at hdr,
    rw mul_assoc at hdr,
    rw hri at hdr, 
    rw mul_one at hdr,
    rw ←hdr at he,
    left,
    use (ri * e),
    rw ← mul_assoc, 
    exact he,
  }
end

theorem pid_is_ufd (R : Type) [hc : comm_ring R] (hpid : is_pid R): is_ufd R:=
begin
  split,
    exact hpid.left,
  split,
  {
    intro f,
    intro h,
    let i := λ(x : ℕ), principal_ideal (f x),
    have hinc : asc_ideal_chain i,
      intro n,
      change principal_ideal (f n) ⊆ principal_ideal (f (n+1)),
      specialize h n,
      cases h with y hy,
      rw hy,
      intros x h2,
      cases h2 with z hz,
      use y * z,
      rw ← mul_assoc,
      exact hz,
    have hnoet := pid_is_noetherian R hpid,
    specialize hnoet i,
    have hstab := hnoet hinc,
    cases hstab with m hm,
    use m,
    intro q,
    specialize hm q,
    intro hmq,
    have hiqs := hm hmq,
    apply generators_associate_if_ideals_eq,
    exact hpid.left,
    exact hiqs,
  },
  {
    exact pid_irreducible_is_prime hpid,
  }
end
#lint