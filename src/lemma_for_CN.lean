import data.mv_polynomial.basic
import data.mv_polynomial.variables
import data.polynomial.eval
import data.polynomial.ring_division
import algebra.big_operators.basic
import data.mv_polynomial.equiv
import logic.is_empty
open nat mv_polynomial finset

set_option trace.simplify.rewrite true

universe u_1

lemma eq_zero_of_enough_roots (F : Type u_1)[field F][decidable_eq F] (n : ℕ) 
  (P : mv_polynomial (fin n) F) (S : fin n → finset F)
  (H1 : ∀ i : (fin n), degree_of i P < (S i).card)
  (H2 : ∀(v : fin n → F), (∀(i:fin n), v i ∈ S i) → eval v P = 0)
  : P = 0 :=
begin
  induction n with n hn, { -- Induktionsstart: ingen variable ækvivalent med blot legeme.
    specialize H2 (fin.is_empty.elim),
    simp at H2,
    have he := is_empty_ring_equiv_apply F (fin 0) P,
    have hd : (aeval (fin.is_empty.elim : fin 0 → F)) P = (eval (fin.is_empty.elim : fin 0 → F)) P := rfl,
    rw hd at he,
    rw ← he at H2,
    rw ← (ring_equiv.map_zero (is_empty_ring_equiv F (fin 0))) at H2,
    exact ring_equiv.injective (is_empty_ring_equiv F (fin 0)) H2,
  }, -- Herfra induktionsskridt:
  let P' := fin_succ_equiv F n P, --Betragter P (i stedet for som polynomium i n+1 variable) som enkeltvariabelt polynomium med koefficienter bestående af polynomier med n variable
  have P'_eq_zero : P' = 0, {
    have P'_eq_zero_of_coeff_eval : ∀(v : fin n → F), (∀(i:fin n), v i ∈ S i.succ) → polynomial.map (eval v) P' = 0, { --At evaluere koefficienterne giver nulpolynomiet
      intros v hv,
      have eval_degree_decreases := polynomial.nat_degree_map_le (eval v) P',
      rw nat_degree_fin_succ_equiv P at eval_degree_decreases,
      have zero_of_eval_eval : ∀ s ∈ S 0, polynomial.eval s (polynomial.map (eval v) P') = 0, { --Evaluering i den sidste variabel efter evaluering af andre variable giver 0
        intros s hs,
        rw ← (mv_polynomial.eval_eq_eval_mv_eval' v s P),
        apply H2,
        intro i,
        by_cases i = 0, { --Noget om elementer i lister, som ikke har noget med polynomier at gøre
          rw h,
          simp *,
        }, {
          cases fin.eq_succ_of_ne_zero h with j hj,
          rw hj,
          rw fin.cons_succ _ _ _,
          exact hv j,
        },
      },
      by_contradiction AFC,
      have roots_of_eval : S 0 ⊆ (polynomial.roots (polynomial.map (eval v) P')).to_finset, {
        intros s hs,
        rw multiset.mem_to_finset,
        rw polynomial.mem_roots AFC,
        exact zero_of_eval_eval s hs,
      },
      -- Sammensætning af en masse uligheder for at bygge modstriden C:
      have le1 := finset.card_le_of_subset roots_of_eval,
      have le2 := multiset.to_finset_card_le (polynomial.map (eval v) P').roots,
      have le3 := polynomial.card_roots' (polynomial.map (eval v) P'),
      have le12 := le_trans le1 le2,
      have le123 := le_trans le12 le3,
      have C := lt_of_le_of_lt le123 (lt_of_le_of_lt eval_degree_decreases (H1 0)),
      apply lt_irrefl (S 0).card,
      exact C,
    },
    apply polynomial.ext, -- Vis ved induktion, at P' får samme koefficienter som 0 ∈ F[x]
    intro i,
    rw polynomial.coeff_zero i, -- Vi svækker induktionshypotesen til de koefficienter, vi har ladet være givet
    specialize hn (P'.coeff i),
    specialize hn (fin.tail S),
    specialize hn (λj, lt_of_le_of_lt (mv_polynomial.degree_of_coeff_fin_succ_equiv P j i) (H1 j.succ)),
    specialize hn begin
      intros v hv,
      specialize P'_eq_zero_of_coeff_eval v hv,
      rw ← polynomial.coeff_map,
      rw P'_eq_zero_of_coeff_eval,
      rw polynomial.coeff_zero,
    end,
    exact hn,
  }, -- Oversæt fra P' til P:
  rw ← alg_equiv.map_zero (fin_succ_equiv F n) at P'_eq_zero,
  exact alg_equiv.injective (fin_succ_equiv F n) P'_eq_zero,
end


 