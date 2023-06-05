import data.finsupp.basic
import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring
import data.mv_polynomial.division
import ring_theory.ideal.basic
import algebra.big_operators.basic
import logic.function.basic
import logic.basic
import monomial_order
import initial_term

noncomputable theory

open_locale big_operators
open mv_polynomial classical

universe u 
variables {σ : Type*} [finite σ] [decidable_eq σ] [term_order σ]
variables {R : Type*} [field R] [decidable_eq R]

-- Assuming (LT f) ∣ (LT g) returns (LT g)/(LT f).
def monomial_div (g f: mv_polynomial σ R) (h : (LT f) ∣ (LT g)) : mv_polynomial σ R :=
  monomial ((IN g) - (IN f)) ((g.coeff (IN g))/(f.coeff (IN f)))
def term (f : mv_polynomial σ R) (c : σ →₀ ℕ) : (mv_polynomial σ R) := monomial c (coeff c f)
lemma non_zero_of_non_constant (s : mv_polynomial σ R) (h : s.degrees ≠ 0) : s ≠ 0 :=
begin
  by_contradiction hs,
  refine h _,
  rw hs,
  exact degrees_zero,
end
lemma monomial_div_nonzero (g f: mv_polynomial σ R) (h : (LT f) ∣ (LT g)) (hg : g ≠ 0) (hf : f ≠ 0) : monomial_div g f h ≠ 0 := begin
  rw monomial_div,
  intro hX,
  rw [monomial_eq_zero, div_eq_zero_iff] at hX,
  cases hX,
  { exact (coeff_IN_nonzero g hg) hX},
  { exact (coeff_IN_nonzero f hf) hX},
end

noncomputable def fin_find' {n : ℕ} (p : fin n → Prop) (h : ∃ i, p i) : fin n :=
  @option.get (fin n) (@fin.find _ (λ i, p i) (dec_pred _)) ((@fin.is_some_find_iff _ _ (dec_pred _)).mpr h)
noncomputable lemma fin_find'_p {n : ℕ} (p : fin n → Prop) (h : ∃ i, p i) : p (fin_find' p h) := begin
  refine @fin.find_spec _ p (dec_pred _) _ _,
  exact option.get_mem _,
end

def mv_div_step {n : ℕ} (f : mv_polynomial σ R) (F : fin n → mv_polynomial σ R)
                        (a : fin n → mv_polynomial σ R) (r : mv_polynomial σ R)
                        (s : mv_polynomial σ R) : 
  (fin n → mv_polynomial σ R) × mv_polynomial σ R × mv_polynomial σ R :=
--         a                        r                  s 
  @dite _ (∃ i:fin n, (LT (F i)) ∣ (LT s)) (prop_decidable _) 
    (λ h, let i := fin_find' (λi, (LT (F i)) ∣ (LT s)) h in
      (function.update a i ((a i) + monomial_div s (F i) (fin_find'_p _ h)), r, s - (monomial_div s (F i) (fin_find'_p _ h))*(F i)))
    (λ h, (a, r + (LT s), s - (LT s)))

lemma mv_div_step_inv1 {n : ℕ}
  (f : mv_polynomial σ R) (F : fin n → mv_polynomial σ R)
  (a : fin n → mv_polynomial σ R) (r : mv_polynomial σ R)
  (s : mv_polynomial σ R)
  (h : f = (∑ i, (a i)*(F i)) + r + s) :
  (f = ∑ i, ((mv_div_step f F a r s).fst i)*(F i) +
        (mv_div_step f F a r s).snd.fst +
        (mv_div_step f F a r s).snd.snd ) := 
  begin
    admit,
  end

lemma coeff_monomial_ne_zero (c m : σ →₀ ℕ) (r : R) (h : ¬(coeff c (monomial m r) = 0)) : m = c := begin
  rw coeff_monomial at h,
  by_contradiction hc,
  simp [hc] at h,
  contradiction,
end
lemma mv_div_step_inv2 {n : ℕ}
  (f : mv_polynomial σ R) (F : fin n → mv_polynomial σ R) 
  (a : fin n → mv_polynomial σ R) (r : mv_polynomial σ R)
  (s : mv_polynomial σ R)
  (h1 : f = (∑i, (a i) * (F i)) + r + s)
  (h2 : r = 0 ∨ ∀(m : fin n) (c ∈ r.support), ¬ LT (F m) ∣ monomial c 1) :
  ((mv_div_step f F a r s).snd.fst = 0 ∨ ∀(m : fin n)(c ∈ (mv_div_step f F a r s).snd.fst.support), ¬ LT (F m) ∣ monomial c 1) :=
begin
  admit,
end

lemma erase_IN (f s : mv_polynomial σ R) (h : (LT f) ∣ (LT s)) (hf : f ≠ 0) (hs : s ≠ 0) (hs' : s - (monomial_div s f h)*f ≠ 0) : IN (s - (monomial_div s f h)*f) < IN s:=
begin
  admit,
end

lemma mv_div_step_decreases {n : ℕ} (f : mv_polynomial σ R)
  (F : fin n → mv_polynomial σ R) :
  Π(a : fin n → mv_polynomial σ R)
  (r : mv_polynomial σ R) (s : mv_polynomial σ R)
  (hs : s ≠ 0),
  (IN' (mv_div_step f F a r s).snd.snd < IN' s)
| a r s hs := begin
  admit,
end

noncomputable def mv_div_aux {n : ℕ} (f : mv_polynomial σ R)
  (F : fin n → mv_polynomial σ R) :
  (fin n → mv_polynomial σ R) ×
  (mv_polynomial σ R) × (mv_polynomial σ R) →
  (fin n → mv_polynomial σ R) × (mv_polynomial σ R) × (mv_polynomial σ R)
| ⟨ a, r, s ⟩  := 
  if hs : s = 0 then
    (a, r, s)
  else
    have (IN' (mv_div_step f F a r s).snd.snd) < (IN' s),
          from mv_div_step_decreases f F a r s hs,
    (mv_div_aux (mv_div_step f F a r s))

  using_well_founded {
    rel_tac := λ _ _, `[exact {
      r := λ N M, IN' N.snd.snd < IN' M.snd.snd,
      wf := (inv_image.is_well_founded _ _).wf
    }],
    dec_tac := `[exact this],
  }

lemma mv_div_aux_s_eq_zero {n : ℕ} (f : mv_polynomial σ R)
  (F : fin n → mv_polynomial σ R) :
  ΠN:(fin n → mv_polynomial σ R) × 
  (mv_polynomial σ R) × (mv_polynomial σ R),
  (mv_div_aux f F N).snd.snd = 0
| ⟨ a, r, s ⟩ := 
  if hs : s = 0 then
    begin
      rw mv_div_aux, simp [hs],
    end
  else
    have (IN' (mv_div_step f F a r s).snd.snd) < (IN' s),
          from mv_div_step_decreases f F a r s hs,
    begin
      rw mv_div_aux, simp [hs],
      exact mv_div_aux_s_eq_zero (mv_div_step f F a r s),
    end
    using_well_founded {
      rel_tac := λ _ _, `[exact {
        r := λN M, IN' N.snd.snd < IN' M.snd.snd,
        wf := (inv_image.is_well_founded _ _).wf,
      }],
      dec_tac := `[exact this],
    }

lemma mv_div_aux_spec1 {n : ℕ} (f : mv_polynomial σ R)
  (F : fin n → mv_polynomial σ R) :
  Π (N:(fin n → mv_polynomial σ R) × 
  (mv_polynomial σ R) × (mv_polynomial σ R))
  (h : f = (∑i, (N.fst i) * (F i)) + N.snd.fst + N.snd.snd ),
  f = (∑i, (mv_div_aux f F N).fst i * F i) + (mv_div_aux f F N).snd.fst + (mv_div_aux f F N).snd.snd
| ⟨ a, r, s ⟩ h :=
  if hs : s = 0 then
    begin
      rw [mv_div_aux],
      simp [hs, h],
    end
  else
    have (IN' (mv_div_step f F a r s).snd.snd) < (IN' s),
      from mv_div_step_decreases f F a r s hs,
    begin
      rw [mv_div_aux],
      simp [hs, h],
      simp at h,
      rw ←h,
      refine mv_div_aux_spec1 (mv_div_step f F a r s) _,
      refine mv_div_step_inv1 f F a r s h,
    end
    using_well_founded {
      rel_tac := λ _ _, `[exact {
        r := λN M, IN' N.fst.snd.snd < IN' M.fst.snd.snd,
        wf := (inv_image.is_well_founded _ _).wf,
      }],
      dec_tac := `[exact this],
    }

lemma coeff_eq_of_nonzero (c : σ →₀ ℕ) (s : mv_polynomial σ R) (H : ¬coeff c (LT s) = 0) : c = IN s := begin
  rw LT at H,
  rw coeff_monomial at H,
  simp at H,
  exact H.1.symm,
end
lemma field_dvd (a b : R) (H : a ≠ 0) : a ∣ b := begin
  existsi a⁻¹ * b,
  rw ←mul_assoc,
  rw mul_inv_cancel H,
  rw one_mul,
end

lemma mv_div_aux_spec2 {n : ℕ} (f : mv_polynomial σ R)
  (F : fin n → mv_polynomial σ R) :
  Π(N:(fin n → mv_polynomial σ R) × 
  (mv_polynomial σ R) × (mv_polynomial σ R))
  (h1 : f = (∑i, (N.fst i) * (F i)) + N.snd.fst + N.snd.snd)
  (h2 : N.snd.fst = 0 ∨ ∀(m : fin n) (c ∈ N.snd.fst.support), ¬ LT (F m) ∣ monomial c 1),
  ((mv_div_aux f F N).snd.fst = 0 ∨ ∀(m : fin n)(c ∈ (mv_div_aux f F N).snd.fst.support), ¬ LT (F m) ∣ monomial c 1)
| ⟨ a, r, s ⟩ h1 h2 := 
  if hs : s = 0 then
    begin
      admit,
    end
  else
    have (IN' (mv_div_step f F a r s).snd.snd) < (IN' s),
      from mv_div_step_decreases f F a r s hs,
    begin
      admit,
    end
    using_well_founded {
      rel_tac := λ _ _, `[exact {
        r := λN M, IN' N.fst.snd.snd < IN' M.fst.snd.snd,
        wf := (inv_image.is_well_founded _ _).wf,
      }],
      dec_tac := `[exact this]
    }

def mv_div {n : ℕ} (f : mv_polynomial σ R) (F : fin n → (mv_polynomial σ R)) :
  (fin n → (mv_polynomial σ R)) × (mv_polynomial σ R) :=
  ((mv_div_aux f F (λ_, 0, 0, f)).fst, (mv_div_aux f F (λ_, 0, 0, f)).snd.fst)
def mv_div_q {n : ℕ} (f : mv_polynomial σ R) (F : fin n → (mv_polynomial σ R)) :
  (fin n → mv_polynomial σ R) := (mv_div f F).fst
def mv_div_r {n : ℕ} (f : mv_polynomial σ R) (F : fin n → (mv_polynomial σ R)) : 
  (mv_polynomial σ R) := (mv_div f F).snd

theorem mv_div_spec1 {n : ℕ} (f : mv_polynomial σ R) (F : fin n → (mv_polynomial σ R)) :
  f = (∑ m : fin n, ((mv_div_q f F) m * (F m))) + (mv_div_r f F) :=
  begin
    rw [mv_div_q, mv_div_r, mv_div],
    simp,
    have C := (mv_div_aux_spec1 f F (λ (_x : fin n), 0, 0, f) begin simp, end),
    have s_eq_0 := (mv_div_aux_s_eq_zero f F (λ (_x : fin n), 0, 0, f)),
    rw [s_eq_0, add_zero] at C,
    exact C,
  end
theorem mv_div_spec2 {n : ℕ} (f : mv_polynomial σ R) (F : fin n → (mv_polynomial σ R)) :
  (mv_div_r f F) = 0 ∨ ∀ (m : fin n) (c ∈ (mv_div_r f F).support), ¬ LT (F m) ∣ monomial c 1 :=
  begin
    rw [mv_div_r, mv_div],
    have C := (mv_div_aux_spec2 f F (λ (_x : fin n), 0, 0, f) begin simp, end),
    simp at C,
    simp,
    exact C,
  end


