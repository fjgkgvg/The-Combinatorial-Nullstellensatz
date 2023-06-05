import init.data.nat.lemmas
import data.nat.choose.dvd
import algebra.ne_zero
import algebra.group.basic
import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring
import data.mv_polynomial.variables
import data.polynomial.eval
import data.polynomial.ring_division
import algebra.big_operators.basic
import data.mv_polynomial.equiv
import logic.is_empty
import lemma_for_CN
import mv_division
open nat mv_polynomial finset

open_locale big_operators

set_option trace.simplify.rewrite true

universe u_1

variables {F : Type u_1} [field F][decidable_eq F]

noncomputable def g {n : ℕ} {F : Type u_1} [field F] (S : finset F) (i : fin n) : mv_polynomial (fin n) F :=
  S.prod (λ s, mv_polynomial.X i - mv_polynomial.C s)
lemma g_def {n : ℕ} {F : Type u_1} [field F] (S : finset F) (i : fin n) : g S i = S.prod (λ s, mv_polynomial.X i - mv_polynomial.C s) := rfl

-- Evaluering af g på et element, hvis i'te indgang ligger i S, giver 0
lemma eval_g_eq_zero {n : ℕ} {F : Type u_1} [field F] (S : finset F) (i : fin n) (v : fin n → F) (hv : v i ∈ S) : eval v (g S i) = 0 := begin
  rw g,
  rw eval_prod,
  apply finset.prod_eq_zero hv,
  have eval_def : ∀ (p : mv_polynomial (fin n) F), mv_polynomial.eval₂ (ring_hom.id F) v p = (mv_polynomial.eval v) p := λ p, rfl,
  rw ← eval_def,
  rw eval₂_sub,
  rw [eval_def, eval_def],
  simp,
end

-- i'te grad af g er (svagt mindre end) størrelsen af det relevante S
lemma degree_of_i_g_eq {n : ℕ} {F : Type u_1} [field F] [term_order (fin n)] [decidable_eq F]
(S : finset F) (i : fin n) : degree_of i (g S i) ≤ S.card := begin
  rw g,
  rw degree_of_def,
  have le1 := degrees_prod S (λ s, mv_polynomial.X i - mv_polynomial.C s),
  have le2 := multiset.count_le_of_le i le1,
  rw multiset.count_sum' at le2,
  simp at le2,
  have le3 : ∑ (x : F) in S, multiset.count i (X i - C x).degrees ≤ ∑ (x : F) in S, multiset.count i ((X i).degrees ⊔ (C x).degrees) := begin
    apply finset.sum_le_sum,
    intros j hj,
    apply multiset.count_le_of_le,
    apply degrees_sub,
  end,
  conv at le3 in ((X i).degrees ⊔ _) {
    rw degrees_C,
    rw degrees_X,
    simp,
    rw multiset.union_def,
    rw multiset.sub_zero,
    simp,
  },
  rw multiset.count_singleton_self at le3,
  simp at le3,
  exact le_trans le2 le3,
end

-- g er aldrig 0-polynomiet...:
lemma g_ne_zero {n : ℕ} {F : Type u_1} [field F] (S : finset F) (i : fin n) : g S i ≠ 0 := begin
  rw g_def,
  rw ne.def,
  rw finset.prod_eq_zero_iff,
  rw not_exists,
  intro x,
  rw not_exists,
  intro hx,
  rw ←ne.def,
  rw mv_polynomial.ne_zero_iff,
  use finsupp.single i 1,
  rw coeff_sub,
  simp,

  have h2 : ¬ 0 = finsupp.single i 1 := begin
    intro contra,
    rw eq_comm at contra,
    simp at contra,
    exact contra,
  end,
  simp [h2],
end

-- For ethvert mv-polynomium er den i'te grad af den ledende term mindre end den i'te grad af polynomiet *Andreas' magi*: 
lemma IN_apply_le_degree_of {n : ℕ} [term_order (fin n)] (f : mv_polynomial (fin n) F) (i : fin n) : (IN f).to_fun i ≤ degree_of i f := begin
  rw IN,
  by_cases hf : f = 0, {
    simp [hf],
    exact @finsupp.zero_apply _ _ _ i,
  }, {
    simp [hf],
    rw degree_of_eq_sup,
    rw finset.max'_eq_sup' _ _,
    rw finset.sup'_eq_sup, 
    
    have fun_eq_to_fun : (∀ (m : fin n →₀ ℕ), m i = m.to_fun i) := λm, rfl,
    conv {
      to_rhs,
      congr,
      skip,
      funext,
      rw fun_eq_to_fun,
    },
    have eta_exp : (f.support.sup id : mv_term (fin n)).to_fun i = (λm : mv_term (fin n), m.to_fun i) (f.support.sup id) := by simp,
    rw eta_exp,
    apply finset.le_sup _,
    rw ←finset.mem_coe,
    rw ←finset.sup'_eq_sup _ id,
    rw ←finset.max'_eq_sup',

    apply finset.max'_mem,

    exact mv_polynomial.non_empty_support_of_ne_zero (f) (hf),
  }
end

-- Initialtermen af g_i har j'te grad 0 for j ≠ i ved at bruge ovenstående ulighed:
lemma IN_g_of_ne {n : ℕ} {F : Type u_1} [field F] [term_order (fin n)] [decidable_eq F]
(S : finset F) (i : fin n) (j : fin n) (h : j ≠ i) : (IN (g S i)).to_fun j = 0 := begin
  have degree_eq_zero : degree_of j (g S i) = 0, {
    rw g,
    rw degree_of_def,
    have le1 := degrees_prod S (λ s, mv_polynomial.X i - mv_polynomial.C s),
    have le2 := multiset.count_le_of_le j le1,
    rw multiset.count_sum' at le2,
    simp at le2,
    have le3 : ∑ (x : F) in S, multiset.count j (X i - C x).degrees ≤ ∑ (x : F) in S, multiset.count j ((X i).degrees ⊔ (C x).degrees) := begin
      apply finset.sum_le_sum,
      intros k hk,
      apply multiset.count_le_of_le,
      apply degrees_sub,
    end,
    conv at le3 in ((X i).degrees ⊔ _) {
      rw degrees_C,
      rw degrees_X,
      simp,
      rw multiset.union_def,
      rw multiset.sub_zero,
      simp,
    },
    rw multiset.count_singleton at le3,
    have if_eq : ite (j = i) 1 0 = 0, {
      simp,
      exact h,
    },
    rw if_eq at le3,
    rw finset.sum_const at le3,
    rw algebra.id.smul_eq_mul at le3,
    rw mul_zero at le3,
    exact nat.eq_zero_of_le_zero (le_trans le2 le3),
  },
  have IN_degree_le_degree := IN_apply_le_degree_of (g S i) j,
  rw degree_eq_zero at IN_degree_le_degree,
  exact nat.eq_zero_of_le_zero IN_degree_le_degree,
end

theorem the_combinatorial_Nullstellensatz (n : ℕ)[term_order (fin n)]
  (S : fin n → finset F) (f : mv_polynomial (fin n) F)
  (hf : ∀(v : fin n → F), (∀(i:fin n), v i ∈ S i) → eval v f = 0):
  ∃ (q : fin n → mv_polynomial (fin n) F), (f = ∑ (i : fin n), q i * (g (S i) i)) := begin
    by_cases hS : (∃ i : fin n, (S i).card = 0), { -- Hvis en af S_i'erne er tomme (urealistisk case)
      cases hS with i hi,
      use (λ j : fin n, if (j = i) then f else 0),
      simp,
      rw g_def,
      rw finset.card_eq_zero at hi,
      rw hi,
      simp,
    }, { -- Hvis alle S_i'erne er beboede:
      rw not_exists at hS,
      let q := mv_div_q f (λ i : fin n, g (S i) i),
      let r := mv_div_r f (λ i : fin n, g (S i) i),
      have r_def : r = mv_div_r f (λ i : fin n, g (S i) i) := rfl,
      use q,
      have r_eq_zero : mv_div_r f (λ i : fin n, g (S i) i) = 0, { -- Efter division med g'erne er resten 0
        have r_degree_lt_card : ∀ i : fin n, degree_of i r < (S i).card, { -- Resten har grad mindre end størrelsen af hvert S_i:
          intro i,
          have r_spec := mv_div_spec2 f (λ i : fin n, g (S i) i),
          cases r_spec, {
            rw ←r_def at r_spec,
            rw r_spec,
            simp,
            specialize hS i,
            exact nat.pos_of_ne_zero hS,
          }, {
            have r_terms_degrees_lt_degrees : ∀ (i : fin n) (c : fin n →₀ ℕ), c ∈ r.support → c i < degree_of i (g (S i) i), { -- i'te grad af en term er mindre end i'te grad af polynomiet
              intros i c hc,
              specialize r_spec i c hc,
              simp at r_spec,
              rw LT at r_spec,
              rw monomial_dvd_monomial at r_spec,
              simp at r_spec,
              have r_spec_conpos := function.mt r_spec,
              rw not_not at r_spec_conpos,
              specialize r_spec_conpos (field_dvd _ 1 (coeff_IN_nonzero _ (g_ne_zero (S i) i))),
              rw finsupp.le_iff at r_spec_conpos,
              simp at r_spec_conpos,
              cases r_spec_conpos with j hj,
              by_cases hji : j = i, {
                rw hji at hj,
                exact lt_of_lt_of_le hj.2 (IN_apply_le_degree_of (g (S i) i) i),
              }, {
                exfalso,
                exact hj.1 (IN_g_of_ne (S i) i j hji),
              }
            },
            have hS' : ∀i : fin n, 0 < (S i).card := λ i, nat.pos_of_ne_zero (hS i),
            rw degree_of_lt_iff (hS' i),
            intros c hc,
            specialize r_terms_degrees_lt_degrees i c hc,
            exact lt_of_lt_of_le r_terms_degrees_lt_degrees (degree_of_i_g_eq (S i) i),
          },
        },
        have f_eq_sum_plus_r := mv_div_spec1 f (λ i : fin n, g (S i) i), -- f kan skrives som divisionsalgoritmen giver det
        rw add_comm at f_eq_sum_plus_r,
        have f_sub_sum_eq_r := sub_eq_of_eq_add f_eq_sum_plus_r,
        rw ←f_sub_sum_eq_r,
        apply eq_zero_of_enough_roots F n _ S, {
          rw f_sub_sum_eq_r,
          rw ←r_def,
          exact r_degree_lt_card,
        }, {
          intros v hv,
          have eval₂_eq_eval : ∀ (p : mv_polynomial (fin n) F), mv_polynomial.eval₂ (ring_hom.id F) v p = (mv_polynomial.eval v) p := λ p, rfl,
          rw [←eval₂_eq_eval, eval₂_sub, eval₂_eq_eval, eval₂_eq_eval],
          rw hf v hv,
          rw eval_sum,
          conv in ((eval v) _) {
            rw ←eval₂_eq_eval,
            rw eval₂_mul,
            rw [eval₂_eq_eval, eval₂_eq_eval],
            congr,
            skip,
            simp,
            rw eval_g_eq_zero (S x) x v (hv x),
          },
          simp,
        },
      },
      have f_eq_sum := mv_div_spec1 f (λ i : fin n, g (S i) i),
      rw r_eq_zero at f_eq_sum,
      rw add_zero at f_eq_sum,
      exact f_eq_sum,
    }
  end