import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Interval.Set.OrderIso
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

open MeasureTheory intervalIntegral
open Polynomial Real
open Real Set
open Set
open intervalIntegral
noncomputable section




/-!
# Simpson Rule
 The approach follows textbook 'An introduction to Numberical Analysis' by Endre Suli and David Mayers, with a little adjustment done, and also the notes of Math3230 'Numerical Analysis' from CUHK.

This file's purpose is to construct the much tighter bound
using the Simpson's rule, which is exact for degree ≤ 3 Polynomial
under the 3 interpolating nodes: a, (a+b)/2 , b.

Where f : ℝ → ℝ is estimated by:
∫ f a..b ≈ S(f;a,b)= (b-a)/6 [f(a) + 4 f((a+b)/2) + f(b)]


The Error Estimation of under simpson rule is mainly
separated into 3 cases:

1: E Found using the lagrange interpolation on f
2:E Found using the Taylor expansion on f
3:E found using the subsequence

## Main Definitions



## Main statements



-/


/-Definition of Simpson Sum for the function f on [a,b] -/
def simpsonSum (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (b - a) / 6 * (f a + 4 * f ((a + b) / 2) + f b)


/-Linearity: Additivity-/
lemma simpsonSum_add (f g : ℝ → ℝ) (a b : ℝ) :
    simpsonSum (f + g) a b = simpsonSum f a b + simpsonSum g a b   := by
  dsimp [simpsonSum]
  ring

/-Linearity : scalar Mul.-/
lemma simpsonSum_smul (c : ℝ) (f : ℝ → ℝ) (a b : ℝ) :
  simpsonSum (fun x => c * f x) a b = c * simpsonSum f a b := by
  dsimp [simpsonSum]
  ring


/-In the section below, we will show the exactness of simpson rule for X^0,X^1,X^2,X^3,
 then use lienarity to show it is exact for arbitrary polynomial of degree ≤ 3-/


/-Show that simpson rule is exact for Monomial X^0-/
lemma simpson_exact_x0 (a b : ℝ) :
    ∫ _x in a..b, (1 : ℝ) = simpsonSum (fun _=>1) a b := by
  dsimp [simpsonSum]
  rw [intervalIntegral.integral_const]
  ring

/-Show that simpson rule is exact for Monomial X^1-/

lemma simpson_exact_x1 (a b : ℝ) :
    ∫ x in a..b, x = simpsonSum (fun x => x) a b := by
  dsimp [simpsonSum]
  rw[integral_id]
  ring

/- Show that simpson rule is exact for Monomial X^2-/
lemma simpson_exact_x2 (a b : ℝ) :
    ∫ x in a..b, x^2 = simpsonSum (fun x => x^2) a b := by
  dsimp [simpsonSum]
  rw [integral_pow 2]
  ring

/- Show that simpson rule is exact for Monomial X^3-/
lemma simpson_exact_x3 (a b : ℝ) :
    ∫ x in a..b, x^3 = simpsonSum (fun x => x^3) a b := by
  dsimp [simpsonSum]
  rw [integral_pow 3]
  ring

/-Show Simpson rule is exact for arbitrary Polynomial of degree ≤ 3-/

lemma eval_le_three (p : ℝ[X]) (hp : p.natDegree ≤ 3) (x : ℝ) :
   p.eval x = p.coeff 0 * 1 + p.coeff 1 * x + p.coeff 2 * x^2 + p.coeff 3 * x^3 := by
   rw[p.eval_eq_sum_range]
   have h4: p.natDegree +1 ≤ 4:= by omega
   have h_sum : ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i =
               ∑ i ∈ Finset.range 4, p.coeff i * x ^ i := by
    apply Finset.sum_subset
    · intro i hi
      rw [Finset.mem_range] at hi ⊢
      omega
    · intro i hi hni
      rw [Finset.mem_range] at hi hni
      have hlt : p.natDegree < i := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, zero_mul]
   rw[h_sum]
   rw[Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ]
   ring

lemma integrable_term (c : ℝ) (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => c * x ^ n) volume a b := by
  exact (continuous_const.mul (continuous_pow n)).intervalIntegrable a b


--Helper function to make the x into x^1 in the integral
lemma integrable_term_one (c : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun x => c * x) volume a b :=
  (continuous_const.mul continuous_id).intervalIntegrable a b


theorem simpson_exact_of_degree_le_three (p : ℝ[X]) (hp : p.natDegree ≤ 3) (a b : ℝ) :
    ∫ x in a..b, p.eval x = simpsonSum (fun x => p.eval x) a b := by
  --Goal: extract each degree in terms of monomial
  simp_rw [eval_le_three p hp]
  have hi0 : IntervalIntegrable (fun x => p.coeff 0 * 1) volume a b :=
    integrable_term (p.coeff 0) 0 a b
  have hi1 : IntervalIntegrable (fun x => p.coeff 1 * x) volume a b :=
    integrable_term_one (p.coeff 1) a b
  have hi2 : IntervalIntegrable (fun x => p.coeff 2 * x^2) volume a b :=
    integrable_term (p.coeff 2) 2 a b
  have hi3 : IntervalIntegrable (fun x => p.coeff 3 * x^3) volume a b :=
    integrable_term (p.coeff 3) 3 a b
  have hi01 : IntervalIntegrable (fun x => p.coeff 0 * 1 + p.coeff 1 * x) volume a b :=
    hi0.add hi1
  have hi012 : IntervalIntegrable
      (fun x => p.coeff 0 * 1 + p.coeff 1 * x + p.coeff 2 * x^2) volume a b :=
    hi01.add hi2
  rw [intervalIntegral.integral_add hi012 hi3]
  rw [intervalIntegral.integral_add hi01 hi2]
  rw [intervalIntegral.integral_add hi0 hi1]
  repeat' rw [intervalIntegral.integral_const_mul]
  dsimp [simpsonSum]
  have h1 : ∫ x in a..b, (1 : ℝ) = (b - a) := by simp [intervalIntegral.integral_const]
  have h2 : ∫ x in a..b, x = (b^2 - a^2) / 2 := by simp [integral_id]
  have h3 : ∫ x in a..b, x^2 = (b^3 - a^3) / 3 := by
   simp [integral_pow 2]
   ring
  have h4 : ∫ x in a..b, x^3 = (b^4 - a^4) / 4 := by
    simp [integral_pow 3]
    ring
  rw [h1, h2, h3, h4]
  ring

/-- a helper function for merging function
lemma convex_merge_ivt {g : ℝ → ℝ} {a b μ₁ μ₂ : ℝ}
    (hab : a < b)
    (h_cont : ContinuousOn g (uIcc a b))
    (hμ₁ : μ₁ ∈ Ioo a b)
    (hμ₂ : μ₂ ∈ Ioo a b) :
    ∃ μ ∈ Ioo a b, g μ₁ + 4 * g μ₂ = 5 * g μ := by
  have h5 : (5 : ℝ) ≠ 0 := by norm_num
  set v := (g μ₁ + 4 * g μ₂) / 5
  have hv : v ∈ uIcc (g μ₁) (g μ₂) := by
    rw [mem_uIcc]
    dsimp[v]
    rcases le_total (g μ₁) (g μ₂) with h | h
    · left
      constructor <;> linarith
    · right
      constructor <;> linarith
  -- 2. Restrict continuity to uIcc μ₁ μ₂
  have h_sub : uIcc μ₁ μ₂ ⊆ Ioo a b := ordConnected_Ioo.uIcc_subset hμ₁ hμ₂
  have h_sub_uIcc : uIcc μ₁ μ₂ ⊆ uIcc a b := by
    rw [uIcc_of_le hab.le]
    exact h_sub.trans Ioo_subset_Icc_self
  -- 3. Apply IVT
  obtain ⟨μ, hμ_in, hgμ⟩ := intermediate_value_uIcc (h_cont.mono h_sub_uIcc) hv
  use μ
  refine ⟨h_sub hμ_in, ?_⟩
  dsimp [v] at hgμ
  linarith
-/
def simpsonAuxG (f : ℝ → ℝ) (m : ℝ) (t : ℝ) : ℝ :=
  (∫ x in (m - t)..(m + t), f x) - (t / 3) * (f (m - t) + 4 * f m + f (m + t))


lemma simpsonAuxG_zero (f : ℝ → ℝ) (m : ℝ) : simpsonAuxG f m 0 = 0 := by
  simp[simpsonAuxG]

--split function in order to use ther FLT
lemma deriv_int_symm (f : ℝ → ℝ) (m t : ℝ) (hf : Continuous f) :
    HasDerivAt (fun t => ∫ x in (m-t)..(m+t), f x)
      (f (m + t) + f (m - t)) t := by
  have h_split : (fun t => ∫ x in (m-t)..(m + t) , f x) =
                 (fun t => (∫ x in m..(m+t), f x)- (∫ x in m..(m-t), f x))  := by
    ext u
    have h1 : IntervalIntegrable f volume (m - u) m := hf.intervalIntegrable _ _
    have h2 : IntervalIntegrable f volume m (m + u) := hf.intervalIntegrable _ _
    rw [← integral_add_adjacent_intervals h1 h2]
    rw [integral_symm (m-u) m]
    ring
  rw [h_split]
  have h_right_base : HasDerivAt (fun u => ∫ x in m..u, f x) (f (m + t)) (m + t) := by
    exact intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable m (m + t))
      (hf.stronglyMeasurableAtFilter volume (nhds (m + t)))
      hf.continuousAt
  have h_shift_right : HasDerivAt (fun t => m + t) 1 t := (hasDerivAt_id t).const_add m
  have h_right : HasDerivAt (fun t => ∫ x in m..(m + t), f x) (f (m + t)) t := by
    convert h_right_base.comp t h_shift_right using 1
    · funext u
      rfl
    · ring
  have h_left_base : HasDerivAt (fun u => ∫ x in m..u, f x) (f (m - t)) (m - t) := by
    exact intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable m (m - t))
      (hf.stronglyMeasurableAtFilter volume (nhds (m - t)))
      (hf.continuousAt)
  have h_shift_left : HasDerivAt (fun t => m - t) (-1) t := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      ((hasDerivAt_id t).neg.const_add m)
  have h_left : HasDerivAt (fun t => ∫ x in m..(m - t), f x) (-f (m - t)) t := by
    convert h_left_base.comp t h_shift_left using 1
    · funext u
      rfl
    · ring
  have h_total : HasDerivAt
      (fun t => (∫ x in m..(m + t), f x) - (∫ x in m..(m - t), f x))
      (f (m + t) + f (m - t)) t := by
    convert h_right.sub h_left using 1
    ring
  simpa using h_total



/-- Step 2: First derivative G'(t) -/
lemma simpsonAuxG_deriv1 (f : ℝ → ℝ) (m t : ℝ) (hf : ContDiff ℝ 1 f) :
    deriv (simpsonAuxG f m) t =
      (2 / 3) * (f (m + t) + f (m - t) - 2 * f m) -
      (t / 3) * (deriv f (m + t) - deriv f (m - t)) := by
  have hf_cont : Continuous f := hf.continuous
  have hf_diff : Differentiable ℝ f := hf.differentiable (by simp)
  have h_int : deriv (fun s => ∫ x in (m - s)..(m + s), f x) t =
      f (m + t) + f (m - t) := (deriv_int_symm f m t hf_cont).deriv
  have h_prod :
      deriv (fun s => (s / 3) * (f (m - s) + 4 * f m + f (m + s))) t =
        (1 / 3) * (f (m - t) + 4 * f m + f (m + t))
          + (t / 3) * (deriv f (m + t) - deriv f (m - t)) := by
    have hl : DifferentiableAt ℝ (fun s => s / 3) t := differentiableAt_id.div_const 3
    have hr : DifferentiableAt ℝ (fun s => (f (m - s) + 4 * f m + f (m + s))) t :=by fun_prop
    change deriv ((fun s : ℝ => s / 3) *
     (fun s => f (m - s) + 4 * f m + f (m + s))) t = _
    rw [deriv_mul hl hr]
    rw [deriv_div_const, deriv_id'']
    have h_1 :
      deriv (fun s : ℝ => f (m - s) + 4 * f m + f (m + s)) t =
        deriv f (m + t) - deriv f (m - t) := by
      have h1 : deriv (fun s : ℝ => f (m - s) ) t = - deriv f (m - t) := by
        have h_inner : HasDerivAt (fun s : ℝ => m - s) (-1) t := by
          simpa [sub_eq_add_neg, add_comm] using
            (hasDerivAt_id t).neg.const_add m
        have h_comp :=
          (hf_diff (m - t)).hasDerivAt.comp t h_inner
        simpa [Function.comp_def] using h_comp.deriv
      have h2 : deriv (fun s : ℝ => f (m + s)) t = deriv f (m + t) := by
        have h_inner : HasDerivAt (fun s : ℝ => m + s) 1 t :=
          (hasDerivAt_id t).const_add m
        have h_comp :=
          (hf_diff (m + t)).hasDerivAt.comp t h_inner
        simpa [Function.comp_def] using h_comp.deriv
      have h3 : DifferentiableAt ℝ (fun s : ℝ  => f (m - s) + 4 * f m) t :=by fun_prop
      have h4 : DifferentiableAt ℝ (fun s : ℝ  => f (m + s)) t := by fun_prop
      rw [deriv_fun_add h3 h4]
      rw [deriv_fun_add (by fun_prop) (by fun_prop)]
      simp [h1, h2]
      ring
    dsimp
    rw [h_1]
  unfold simpsonAuxG
  rw [← Pi.sub_def]
  have h_int_hasDerivAt :
      HasDerivAt (fun s => ∫ x in (m - s)..(m + s), f x)
        (f (m + t) + f (m - t)) t :=
    deriv_int_symm f m t hf_cont
  have h_int := h_int_hasDerivAt.deriv
  have h1 : DifferentiableAt ℝ
      (fun s => ∫ x in (m - s)..(m + s), f x) t :=
    h_int_hasDerivAt.differentiableAt
  have h2 : DifferentiableAt ℝ (fun s ↦ s / 3 * (f (m - s) + 4 * f m + f (m + s))) t := by
    fun_prop
  rw [deriv_sub h1 h2]
  rw [h_int, h_prod]
  ring



lemma deriv2_symm (f : ℝ → ℝ) (m t : ℝ) (hff : ContDiff ℝ 2 f) :
    HasDerivAt (fun s => deriv f (m + s) - deriv f (m - s))
    (iteratedDeriv 2 f (m + t) + iteratedDeriv 2 f (m - t)) t := by
  rw [← Pi.sub_def]
  have hdf : Differentiable ℝ (deriv f) := hff.differentiable_deriv_two
  have hd : Differentiable ℝ f := hff.differentiable (by simp)
  have h1 : HasDerivAt (fun s : ℝ => deriv f (m + s))
      (deriv (deriv f) (m + t)) t := by
    have h1i : HasDerivAt (fun s : ℝ => m + s) 1 t :=
      (hasDerivAt_id t).const_add m
    simpa [Function.comp_def] using (hdf (m + t)).hasDerivAt.comp t h1i
  have h2 : HasDerivAt (fun s : ℝ => deriv f (m-s))
      (-(deriv (deriv f) (m - t))) t := by
    have h2i : HasDerivAt (fun s : ℝ => m - s) (-1) t := by
      simpa [sub_eq_add_neg, add_comm] using
      (hasDerivAt_id t).neg.const_add m
    simpa [Function.comp_def] using (hdf (m - t)).hasDerivAt.comp t h2i
  have h_sub := h1.sub h2
  simpa [iteratedDeriv_succ, iteratedDeriv_one] using h_sub




lemma simpsonAuxG_deriv1_zero (f : ℝ → ℝ) (m : ℝ) (hf : ContDiff ℝ 1 f) :
    deriv (simpsonAuxG f m) 0 = 0 := by
  rw [simpsonAuxG_deriv1 f m 0 hf]
  ring_nf

/-- Step 3: Second derivative G''(t) -/
lemma simpsonAuxG_deriv2 (f : ℝ → ℝ) (m t : ℝ) (hf : ContDiff ℝ 2 f) :
    iteratedDeriv 2 (simpsonAuxG f m) t =
      (1 / 3) * (deriv f (m + t) - deriv f (m - t)) -
      (t / 3) * (iteratedDeriv 2 f (m + t) + iteratedDeriv 2 f (m - t)) := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have h1 : HasDerivAt (fun s => deriv f (m + s) - deriv f (m - s))
    (iteratedDeriv 2 f (m + t) + iteratedDeriv 2 f (m - t)) t := deriv2_symm f m t hf
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num )
  have h_eq : deriv (simpsonAuxG f m) =
      (fun s => (2 / 3) * (f (m + s) + f (m - s) - 2 * f m) -
            (s / 3) * (deriv f (m + s) - deriv f (m - s))) := by
    funext s
    exact simpsonAuxG_deriv1 f m s hf1
  have hii : iteratedDeriv 2 (simpsonAuxG f m) =
      deriv (deriv (simpsonAuxG f m)) := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num]
    rw[iteratedDeriv_succ, iteratedDeriv_one]
  rw[hii, h_eq]
  have hp : HasDerivAt (fun s : ℝ => f (m + s))
      (deriv f (m + t)) t := by
    have hi : HasDerivAt (fun s : ℝ => m+s) 1 t :=
      (hasDerivAt_id t).const_add m
    simpa [Function.comp_def] using
    (hd (m+t)).hasDerivAt.comp t hi
  have hm : HasDerivAt (fun s : ℝ => f (m - s))
      (-deriv f (m - t)) t := by
    have hi : HasDerivAt (fun s : ℝ => m - s) (-1) t := by
      simpa [sub_eq_add_neg, add_comm] using
        (hasDerivAt_id t).neg.const_add m
    simpa [Function.comp_def] using
      (hd (m - t)).hasDerivAt.comp t hi
  have hc : HasDerivAt (fun s : ℝ => 2 * f m ) 0 t :=
    hasDerivAt_const t _
  have hA : HasDerivAt
      (fun s : ℝ => (2/3) * (f (m+s)+f (m-s) - 2 * f m))
      ((2/3) * (deriv f (m + t) - deriv f (m - t))) t := by
    have hsum := (hp.add hm).sub hc
    convert hsum.const_mul (2 / 3) using 1
    · ring
  have hProd : HasDerivAt
      (fun s : ℝ => s / 3 * (deriv f (m + s) - deriv f (m - s)))
      ((1 / 3) * (deriv f (m + t) - deriv f (m - t)) +
        (t / 3) * (iteratedDeriv 2 f (m + t) +
          iteratedDeriv 2 f (m - t))) t := by
    convert ((hasDerivAt_id t).div_const 3).mul h1 using 1
    · funext s
      rfl
    · simp only [id_eq]
  rw [← Pi.sub_def]
  rw [(hA.sub hProd).deriv]
  ring

lemma simpsonAuxG_deriv2_zero (f : ℝ → ℝ) (m : ℝ) (hf : ContDiff ℝ 2 f) :
    iteratedDeriv 2 (simpsonAuxG f m) 0 = 0 := by
  rw [simpsonAuxG_deriv2 f m 0 hf]
  ring_nf

/-- Step 4: Third derivative G'''(t) - cancelations leave a single difference term -/
lemma simpsonAuxG_deriv3 (f : ℝ → ℝ) (m t : ℝ) (hf : ContDiff ℝ 4 f) :
    iteratedDeriv 3 (simpsonAuxG f m) t =
      - (t / 3) * (iteratedDeriv 3 f (m + t) - iteratedDeriv 3 f (m - t)) := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num )
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num )
  have hdf : Differentiable ℝ (iteratedDeriv 2 f) :=
    hf.differentiable_iteratedDeriv 2 (by norm_num)
  have hdf2 : Differentiable ℝ (iteratedDeriv 1 f) :=
    hf.differentiable_iteratedDeriv 1 (by norm_num)
  have h_eq1 : deriv (simpsonAuxG f m) =
      (fun s => (2 / 3) * (f (m + s) + f (m - s) - 2 * f m) -
            (s / 3) * (deriv f (m + s) - deriv f (m - s))) := by
    funext s
    exact simpsonAuxG_deriv1 f m s hf1
  have h_eq : iteratedDeriv 2 (simpsonAuxG f m) =
      (fun s => (1 / 3) * (deriv f (m + s) - deriv f (m - s)) -
      (s / 3) * (iteratedDeriv 2 f (m + s) + iteratedDeriv 2 f (m - s))) := by
    funext s
    exact simpsonAuxG_deriv2 f m s hf2
  have hii2 : iteratedDeriv 3 (simpsonAuxG f m) =
      deriv (iteratedDeriv 2 ( simpsonAuxG f m)):= by
    rw [show (3 : ℕ ) = 1 + 1 + 1 by norm_num]
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hii2, h_eq]
  have h_d1 : HasDerivAt (fun s : ℝ => iteratedDeriv 2 f (m + s))
        (deriv (iteratedDeriv 2 f) (m + t)) t := by
    have h_inner : HasDerivAt ( fun s : ℝ => m + s) 1 t := (hasDerivAt_id t).const_add m
    simpa [Function.comp_def, iteratedDeriv_succ] using (hdf (m + t)).hasDerivAt.comp t h_inner
  have h_d2 : HasDerivAt (fun s : ℝ => iteratedDeriv 2 f (m - s))
        (-(deriv (iteratedDeriv 2 f) (m - t))) t := by
    have h_inner : HasDerivAt ( fun s : ℝ => m - s) (-1) t :=by
      simpa [sub_eq_add_neg, add_comm] using (hasDerivAt_id t).neg.const_add m
    simpa [Function.comp_def, iteratedDeriv_succ] using (hdf (m - t)).hasDerivAt.comp t h_inner
  rw [← Pi.sub_def]
  have h_1 : HasDerivAt (fun s : ℝ => deriv f (m + s) ) (iteratedDeriv 2 f (m + t)) t := by
    have h_inner : HasDerivAt (fun s : ℝ => m + s) 1 t := (hasDerivAt_id t).const_add m
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    simpa [Function.comp_def] using (hdf2 (m + t)).hasDerivAt.comp t h_inner
  have h_2 : HasDerivAt (fun s :ℝ => deriv f (m - s)) (- iteratedDeriv 2 f (m - t)) t := by
    have h_inner : HasDerivAt ( fun s : ℝ => m - s) (-1) t :=by
      simpa [sub_eq_add_neg, add_comm] using (hasDerivAt_id t).neg.const_add m
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    simpa [Function.comp_def, iteratedDeriv_succ] using (hdf2 (m - t)).hasDerivAt.comp t h_inner
  have hA : HasDerivAt
      (fun s => deriv f (m + s) - deriv f (m - s))
      (iteratedDeriv 2 f (m + t) + iteratedDeriv 2 f (m - t)) t := by
    convert h_1.sub h_2 using 1
    ring
  have hB : HasDerivAt
      (fun s => iteratedDeriv 2 f (m + s) + iteratedDeriv 2 f (m - s))
      (iteratedDeriv 3 f (m + t) - iteratedDeriv 3 f (m - t)) t := by
    convert h_d1.add h_d2 using 1
    simp only [iteratedDeriv_succ]
    ring
  have hProd : HasDerivAt
      (fun s => s / 3 *
        (iteratedDeriv 2 f (m + s) + iteratedDeriv 2 f (m - s)))
      ((1 / 3) * (iteratedDeriv 2 f (m + t) + iteratedDeriv 2 f (m - t)) +
        (t / 3) * (iteratedDeriv 3 f (m + t) - iteratedDeriv 3 f (m - t))) t := by
    convert ((hasDerivAt_id t).div_const 3).mul hB using 1
    · funext s
      rfl
    · simp only [id_eq]
  have h_first : HasDerivAt
      (fun s => (1 / 3) * (deriv f (m + s) - deriv f (m - s)))
      ((1 / 3) * (iteratedDeriv 2 f (m + t) + iteratedDeriv 2 f (m - t))) t :=
    hA.const_mul (1 / 3)
  have h_result := h_first.sub hProd
  rw [h_result.deriv]
  ring

theorem simpson_error_estimation_taylor
    (f : ℝ → ℝ) (a b : ℝ)
    (hab : a < b)
    (h_smooth : ContDiff ℝ 4 f) :
    ∃ ζ ∈ uIcc a b,
      (∫ x in a..b, f x) - ((b - a) / 6) * (f a + 4 * f ((a + b) / 2) + f b) =
      - ((b - a) ^ 5 / 2880) * iteratedDeriv 4 f ζ := by
  set m := (a + b) / 2
  set h := (b - a) / 2
  --Define F(x) = ∫ x in a..x , f t and use FTC for deri of F
  -- Taylor expansion of F(b) up to order 5
  -- Taylor expansion of f(m), f(b) up to order ≤ 4
  -- subtractr and cancel term from 0 to 3 using ring
  -- merge using the helper function
  sorry
