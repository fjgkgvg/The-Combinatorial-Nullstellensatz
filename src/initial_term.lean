import data.nat.basic
import init.algebra.order
import set_theory.cardinal.finite
import data.vector.zip
import data.finsupp.basic
import data.finite.defs
import data.finset.basic
import data.finset.lattice
import data.finsupp.defs
import data.mv_polynomial.basic
import ring_theory.polynomial.basic
import monomial_order

universe u 
variables {σ : Type u } {R : Type*} [field R] [finite σ] [decidable_eq σ] [decidable_eq R]

noncomputable theory

open mv_polynomial

def IN {σ : Type u} [decidable_eq σ] [finite σ] [term_order σ] (f : mv_polynomial σ R) : (mv_term σ) :=
  if h : (f = 0) then
    0
  else 
    finset.max' f.support (mv_polynomial.non_empty_support_of_ne_zero f h)
def IN' {σ : Type u} [decidable_eq σ] [finite σ] [term_order σ] (f : mv_polynomial σ R) : with_bot (mv_term σ) :=
  if h : f = 0 then
    ⊥
  else
    ↑(IN f)
def LT {σ : Type u} [decidable_eq σ] [finite σ] [term_order σ] (f : mv_polynomial σ R) : (mv_polynomial σ R) :=
  mv_polynomial.monomial (IN f) (f.coeff (IN f))

set_option trace.simplify.rewrite true
lemma IN'_eq_IN {σ : Type u} [decidable_eq σ] [finite σ] [term_order σ] (f : mv_polynomial σ R) (h : f ≠ 0) :
  IN' f = ↑(IN f) := begin
    rw IN',
    simp [h],
  end
lemma IN'_eq_bot {σ : Type u} [decidable_eq σ] [finite σ] [term_order σ] (f : mv_polynomial σ R) (h : f = 0) :
  IN' f = ⊥ := begin
    rw IN',
    simp [h],
  end

lemma IN_of_non_zero_eq {σ : Type u} [decidable_eq σ] [finite σ] [term_order σ] (f : mv_polynomial σ R) (h : f ≠ 0) :
  IN f = finset.max' f.support (mv_polynomial.non_empty_support_of_ne_zero f h):= begin
    rw IN,
    simp [h],
  end
lemma coeff_IN_nonzero [term_order σ] (f : mv_polynomial σ R) (h : f ≠ 0) :
  coeff (IN f) f ≠ 0 := begin
    rw [←mv_polynomial.mem_support_iff, IN_of_non_zero_eq _ h],
    exact finset.max'_mem _ _,
  end
lemma IN_mem_support [term_order σ] (f : mv_polynomial σ R) (hf : f ≠ 0) :
IN f ∈ f.support := begin
  rw IN,
  simp only [hf, not_false_iff, dif_neg],
  exact finset.max'_mem _ _,
end
@[simp]
lemma IN_neg [term_order σ] (f : mv_polynomial σ R) : IN (-f) = IN f := begin
  rw [IN, IN],
  by_cases f = 0, {
    have h' : -f = 0 := by simp [h],
    simp [h, h'],
  }, {
    have h' : ¬(-f = 0) := by simp [h],
    simp [h, h'], 
  }
end
lemma IN_add_le_max [term_order σ] (f g : mv_polynomial σ R) (hf : f ≠ 0) (hg : g ≠ 0) :
IN (f+g) ≤ max (IN f) (IN g) := begin
  simp,
  by_cases h : f+g = 0, {
    rw h,
    left,
    exact term_order.zero_le _,
  }, {
    have IN_fg : IN (f+g) ∈ (f+g).support := IN_mem_support _ (h),
    have IN_fug := finset.mem_of_subset mv_polynomial.support_add IN_fg,
    rw finset.mem_union at IN_fug,
    cases IN_fug, {
      left,
      conv in (IN f) {rw IN,},
      simp [hf],
      exact finset.le_max' _ _ IN_fug,
    }, {
      right,
      conv in (IN g) {rw IN,},
      simp [hg],
      exact finset.le_max' _ _ IN_fug,
    }
  }
end
@[simp]
lemma IN_zero [term_order σ] : IN (0 : mv_polynomial σ R) = 0 := begin
  rw IN,
  simp,
end
@[simp]
lemma LT_zero [term_order σ] : LT (0 : mv_polynomial σ R) = 0 := begin
  rw LT,
  simp,
end
@[simp]
lemma IN_monomial [term_order σ] (s : σ →₀ ℕ) (c : R) (hc : c ≠ 0) : IN (monomial s c) = s := begin
  rw IN,
  simp [hc],
  conv in (((monomial s) c).support) {rw support_monomial},
  simp [hc],
end
@[simp]
lemma IN_mul [term_order σ] (f : mv_polynomial σ R) (hf : f ≠ 0) (s : σ →₀ ℕ) (c : R) (hc : c ≠ 0) :
IN ((monomial s c)*f) = IN (monomial s c) + IN f := begin
  rw [IN_monomial _ _ hc, IN],
  have H : monomial s c * f ≠ 0 := begin
    intro hX,
    rw ←zero_mul f at hX,
    have hX' := is_domain.mul_right_cancel_of_ne_zero hf hX,
    rw monomial_eq_zero at hX',
    exact hc hX',
  end,
  simp [H],
  conv in (monomial s c * f) {rw mv_polynomial.mul_def},
  simp [H],
  apply eq_of_le_of_not_lt, {
    refine finset.max'_le _ _ _ _,
    intros y hy,
    have hy' := finset.mem_of_subset (finsupp.support_sum) hy,
    rw finset.mem_bUnion at hy',
    rcases hy' with ⟨i, hi, hy'⟩,
    have hy'' := finset.mem_of_subset (support_monomial_subset) hy',
    rw finset.mem_singleton at hy'',
    rw [IN, hy''],
    simp [hf],
    apply term_order.additive,
    exact finset.le_max' _ _ hi,
  }, {
    intro hX,
    rw finset.max'_lt_iff at hX,
    specialize hX (s + IN f),
    apply @eq.not_lt _ _ (s + IN f : mv_term σ) (s + IN f : mv_term σ) rfl,
    apply hX,
    rw [mv_polynomial.mem_support_iff, sum_def, coeff_sum],
    simp [hc],
    exact coeff_IN_nonzero f hf,
  }
end

lemma erase_IN' [term_order σ] (f s : mv_polynomial σ R) (hf : f ≠ 0) (hs : s ≠ 0) (hsf : s - f ≠ 0) (h : LT f = LT s) : IN (s - f) ≠ IN s:= begin
  suffices h2 : coeff (IN s) (s - f) = 0, {
    intro hX,
    have h2' := coeff_IN_nonzero (s - f) hsf,
    rw hX at h2',
    exact h2' h2,
  },
  rw [LT, LT, monomial_eq_monomial_iff] at h,
  rw [sub_eq_add_neg, coeff_add, coeff_neg],
  cases h, {
    cases h with hIN h_coeff,
    nth_rewrite 0 ←h_coeff,
    rw [hIN, add_neg_self],
  }, {
    exfalso,
    exact coeff_IN_nonzero f hf h.1,
  }
end

lemma nonzero_of_LT_nonzero [term_order σ] (f : mv_polynomial σ R) (h : LT f ≠ 0) : f ≠ 0 := begin
  intro hX,
  rw [hX, LT_zero] at h,
  exact h rfl,
end
lemma eq_zero_of_LT_eq_zero [term_order σ] (f : mv_polynomial σ R) (h : LT f = 0) : f = 0 := begin
  by_contra hX,
  rw [LT, monomial_eq_zero] at h,
  exact coeff_IN_nonzero f hX (h),
end