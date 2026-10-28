import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open Polynomial
noncomputable section

/-!
# Simpson's rule

This file defines Simpson's quadrature sum on a real interval. It proves
that the rule is exact for real polynomials of degree at most three and
establishes the classical error formula for functions that are four times
continuously differentiable on `ℝ`.

## Proof idea

For the error formula, the proof centers the interval at its midpoint and
considers the error on symmetric subintervals. It subtracts a suitable
degree-five polynomial from this auxiliary error function, applies Rolle's
theorem repeatedly, and then applies the mean value theorem to obtain the
fourth-derivative remainder.

## References

* E. Suli and D. Mayers, *An Introduction to Numerical Analysis*.
-/

/-- Simpson's quadrature sum for `f` on the interval with endpoints `a` and `b`. -/
def simpsonSum (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (b - a) / 6 * (f a + 4 * f ((a + b) / 2) + f b)


/-- Simpson's quadrature sum is additive in its integrand. -/
lemma simpsonSum_add (f g : ℝ → ℝ) (a b : ℝ) :
    simpsonSum (f + g) a b = simpsonSum f a b + simpsonSum g a b   := by
  dsimp [simpsonSum]
  ring

/-- Simpson's quadrature sum commutes with scalar multiplication. -/
lemma simpsonSum_smul (c : ℝ) (f : ℝ → ℝ) (a b : ℝ) :
  simpsonSum (fun x => c * f x) a b = c * simpsonSum f a b := by
  dsimp [simpsonSum]
  ring

private lemma integrable_term (c : ℝ) (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => c * x ^ n) MeasureTheory.volume a b := by
  exact (continuous_const.mul (continuous_pow n)).intervalIntegrable a b

/-- Simpson's rule is exact for real polynomials of degree at most three. -/
theorem simpson_exact_of_degree_le_three (p : ℝ[X]) (hp : p.natDegree ≤ 3) (a b : ℝ) :
    ∫ x in a..b, p.eval x = simpsonSum (fun x => p.eval x) a b := by
  have h4 : p.natDegree < 4 := by omega
  dsimp [simpsonSum]
  simp_rw [p.eval_eq_sum_range' h4]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, zero_add, pow_zero, pow_one]
    --AI asked for property of Finset
    repeat' rw [intervalIntegral.integral_const_mul]
    have h0 : ∫ x in a..b, (1 : ℝ) = b - a := by simp [intervalIntegral.integral_const]
    have h1 : ∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2 := by simp [integral_id]
    have h2 : ∫ x in a..b, x ^ 2 = (b ^ 3 - a ^ 3) / 3 := by simp [integral_pow 2]; ring
    have h3 : ∫ x in a..b, x ^ 3 = (b ^ 4 - a ^ 4) / 4 := by simp [integral_pow 3]; ring
    rw [h0, h1, h2, h3]
    ring
  · intro i _
    exact integrable_term (p.coeff i) i a b






private def simpsonAuxG (f : ℝ → ℝ) (m : ℝ) (t : ℝ) : ℝ :=
  (∫ x in (m - t)..(m + t), f x) - (t / 3) * (f (m - t) + 4 * f m + f (m + t))

/-
Helper functions that shows G(0)=G'(0)=G''(0)=0 -/

private lemma simpsonAuxG_zero (f : ℝ → ℝ) (m : ℝ) : simpsonAuxG f m 0 = 0 := by
  simp[simpsonAuxG]

--split function in order to use ther FLT

private lemma deriv_int_symm (f : ℝ → ℝ) (m t : ℝ) (hf : Continuous f) :
    HasDerivAt (fun t => ∫ x in (m-t)..(m+t), f x)
      (f (m + t) + f (m - t)) t := by
  have h_FTC (u : ℝ) : HasDerivAt (fun s => ∫ x in m..s, f x) (f u) u :=
    intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable _ _ )
      (hf.stronglyMeasurableAtFilter _ _ )
      hf.continuousAt
  have hR : HasDerivAt (fun t => ∫ x in m..(m + t), f x) (f (m + t)) t := by
    simpa [Function.comp_def] using (h_FTC (m + t)).comp t ((hasDerivAt_id t).const_add m)
  have hL : HasDerivAt (fun t => ∫ x in m.. (m - t) , f x) (-f (m - t)) t := by
    simpa [Function.comp_def] using (h_FTC (m - t)).comp t ((hasDerivAt_id t).neg.const_add m)
  have h_split : (fun t => ∫ x in (m-t)..(m + t) , f x) =
                 (fun t => (∫ x in m..(m+t), f x)- (∫ x in m..(m-t), f x))  := by
    ext u
    rw[intervalIntegral.integral_symm (m-u) m]
    rw[← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (m-u) m) (hf.intervalIntegrable m (m + u))]
    ring
  rw [h_split]
  convert hR.sub hL using 1
  ring



/-- Step 2: First derivative G'(t) -/
private lemma simpsonAuxG_deriv1 (f : ℝ → ℝ) (m t : ℝ) (hf : ContDiff ℝ 1 f) :
    deriv (simpsonAuxG f m) t =
      (2 / 3) * (f (m + t) + f (m - t) - 2 * f m) -
      (t / 3) * (deriv f (m + t) - deriv f (m - t)) := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have h1 := (hd (m + t)).hasDerivAt.comp t ((hasDerivAt_id t).const_add m)
  have h2 := (hd (m - t)).hasDerivAt.comp t ((hasDerivAt_id t).neg.const_add m)
  have h_prod := ((hasDerivAt_id t).div_const 3).mul
    ((h2.add (hasDerivAt_const t (4 * f m))).add h1)
  have h_G : HasDerivAt (simpsonAuxG f m) _ t := (deriv_int_symm f m t hf.continuous).sub h_prod
  rw [h_G.deriv]
  dsimp
  ring


private lemma deriv2_symm (f : ℝ → ℝ) (m t : ℝ) (hff : ContDiff ℝ 2 f) :
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




private lemma simpsonAuxG_deriv1_zero (f : ℝ → ℝ) (m : ℝ) (hf : ContDiff ℝ 1 f) :
    deriv (simpsonAuxG f m) 0 = 0 := by
  rw [simpsonAuxG_deriv1 f m 0 hf]
  ring_nf

/-- Step 3: Second derivative G''(t) -/
private lemma simpsonAuxG_deriv2 (f : ℝ → ℝ) (m t : ℝ) (hf : ContDiff ℝ 2 f) :
    iteratedDeriv 2 (simpsonAuxG f m) t =
      (1 / 3) * (deriv f (m + t) - deriv f (m - t)) -
      (t / 3) * (iteratedDeriv 2 f (m + t) + iteratedDeriv 2 f (m - t)) := by
  have hd : Differentiable ℝ f:= hf.differentiable (by simp)
  have hp := (hd (m + t)).hasDerivAt.comp t ((hasDerivAt_id t).const_add m)
  have hm := (hd (m - t)).hasDerivAt.comp t ((hasDerivAt_id t).neg.const_add m)
  have hc := ((hp.add hm).sub (hasDerivAt_const t (2 * f m))).const_mul (2/3)
  have hb := ((hasDerivAt_id t).div_const 3).mul (deriv2_symm f m t hf)
  have hd : deriv (simpsonAuxG f m) =
      (fun y => (2 / 3) * (f (m + y) + f (m - y) - 2 * f m)) -
      ((fun x => id x / 3) * (fun s => deriv f (m + s) - deriv f (m - s))) := by
    funext s
    exact simpsonAuxG_deriv1 f m s (hf.of_le (by norm_num))
  have h_lhs : iteratedDeriv 2 (simpsonAuxG f m) t = deriv (deriv (simpsonAuxG f m)) t := by
    simp [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
  rw[h_lhs]
  simp [Function.comp_def] at hc
  rw [hd, (hc.sub hb).deriv]
  simp [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
  ring_nf





private lemma simpsonAuxG_deriv2_zero (f : ℝ → ℝ) (m : ℝ) (hf : ContDiff ℝ 2 f) :
    iteratedDeriv 2 (simpsonAuxG f m) 0 = 0 := by
  rw [simpsonAuxG_deriv2 f m 0 hf]
  ring_nf

/-- Step 4: Third derivative G'''(t) - cancelations leave a single difference term -/
private lemma simpsonAuxG_deriv3 (f : ℝ → ℝ) (m t : ℝ) (hf : ContDiff ℝ 4 f) :
    iteratedDeriv 3 (simpsonAuxG f m) t =
      - (t / 3) * (iteratedDeriv 3 f (m + t) - iteratedDeriv 3 f (m - t)) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num )
  have hd3 := hf.differentiable_iteratedDeriv 2 (by norm_num)
  have h1 := (hd3 (m + t)).hasDerivAt.comp t ((hasDerivAt_id t).const_add m)
  have h2 := (hd3 (m - t)).hasDerivAt.comp t ((hasDerivAt_id t).neg.const_add m)
  simp only [Function.comp_def] at h1 h2 --else there is problem
  have hb1 := (deriv2_symm f m t hf2).const_mul (1 / 3)
  have hb2 := ((hasDerivAt_id t).div_const 3).mul (h1.add h2)
  have h_eq : iteratedDeriv 2 (simpsonAuxG f m) =
      (fun y => (1 / 3) * (deriv f (m + y) - deriv f (m - y))) -
      (fun x => id x / 3) *( (fun s => iteratedDeriv 2 f (m + s))
      + (fun s => iteratedDeriv 2 f (m - s))) := by
    funext s
    dsimp
    exact simpsonAuxG_deriv2 f m s hf2
  have h_lhs : iteratedDeriv 3 (simpsonAuxG f m) t =
      deriv (iteratedDeriv 2 (simpsonAuxG f m)) t := by
    simp [show (3 : ℕ) = 1 + 2 by norm_num, iteratedDeriv_succ]
  rw[h_lhs]
  rw [h_eq, (hb1.sub hb2).deriv]
  dsimp
  simp only [show (3 : ℕ) = 1 + 2 by norm_num, show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
  ring

private lemma exists_third_deriv_eq_zero {F : ℝ → ℝ} {h : ℝ} (hh : 0 < h)
    (hF0 : F 0 = 0) (hFh : F h = 0)
    (hF'0 : deriv F 0 = 0) (hF''0 : iteratedDeriv 2 F 0 = 0)
    (hF_cont : ContinuousOn F (Set.Icc 0 h))
    (hF'_cont : ContinuousOn (deriv F) (Set.Icc 0 h))
    (hF''_cont : ContinuousOn (iteratedDeriv 2 F) (Set.Icc 0 h)) :
    ∃ ξ ∈ Set.Ioo 0 h, iteratedDeriv 3 F ξ = 0 := by
  obtain ⟨ξ₁, hξ₁, hF'1⟩ := exists_deriv_eq_zero hh hF_cont (by rw [hF0, hFh])
  have h1 : Set.Icc 0 ξ₁ ⊆ Set.Icc 0 h := Set.Icc_subset_Icc le_rfl hξ₁.2.le
  obtain ⟨ξ₂, hξ₂, hF''1⟩ := exists_deriv_eq_zero hξ₁.1 (hF'_cont.mono h1) (by rw [hF'0, hF'1])
  have h2 : Set.Icc 0 ξ₂ ⊆ Set.Icc 0 h := Set.Icc_subset_Icc le_rfl (hξ₂.2.le.trans hξ₁.2.le)
  -- Step 1: Turn `deriv (deriv F)` into `deriv (iteratedDeriv 1 F)` then `iteratedDeriv 2 F`
  rw [← iteratedDeriv_one, ← iteratedDeriv_one,iteratedDeriv_one, ←iteratedDeriv_succ] at hF''1
  norm_num at hF''1
  obtain ⟨ξ₃, hξ₃, hF'''1⟩ := exists_deriv_eq_zero hξ₂.1 (hF''_cont.mono h2) (hF''0.trans hF''1.symm)
  -- Step 2: Turn `deriv (iteratedDeriv 2 F)` into `iteratedDeriv 3 F`
  rw [← iteratedDeriv_succ] at hF'''1
  exact ⟨ξ₃, ⟨hξ₃.1, hξ₃.2.trans (hξ₂.2.trans hξ₁.2)⟩, hF'''1⟩


set_option maxHeartbeats 1000000 in
/--
For `f : ℝ → ℝ` with four continuous derivatives and `a < b`, there is a point
`ζ` in `[a, b]` such that the error in Simpson's rule is
`-((b - a)^5 / 2880) * iteratedDeriv 4 f ζ`.
-/
theorem simpson_error_estimation
    (f : ℝ → ℝ) (a b : ℝ)
    (hab : a < b)
    (h_smooth : ContDiff ℝ 4 f) :
    ∃ ζ ∈ Set.uIcc a b,
      (∫ x in a..b, f x) - ((b - a) / 6) * (f a + 4 * f ((a + b) / 2) + f b) =
      - ((b - a) ^ 5 / 2880) * iteratedDeriv 4 f ζ := by
  set m := (a + b) / 2
  set h := (b - a) / 2
  have h_left : m - h = a := by
    dsimp [m, h]
    ring
  have h_right : m + h = b := by
    dsimp [m, h]
    ring
  have h_mid : m = (a + b) / 2 := rfl
  have h_error :
      (∫ t in a..b, f t) -
        ((b - a) / 6) * (f a + 4 * f ((a + b) / 2) + f b) =
        simpsonAuxG f m h := by
    rw [simpsonAuxG, h_left, h_right, h_mid]
    dsimp [h]
    ring
  have h_scale : (b - a) ^ 5 / 2880 = h ^ 5 / 90 := by
    dsimp [h]
    ring
  rw [h_error]
  rw [h_scale]
  have hh: 0 < h := by
    dsimp [h]
    linarith
  let G : ℝ → ℝ := simpsonAuxG f m
  let c : ℝ := G h / h ^ 5
  let P : ℝ → ℝ := fun t => c * t ^ 5
  let F : ℝ → ℝ := fun t => G t - P t
  have F_0_0 : F 0 = 0 := by
    simp [F,G,P,simpsonAuxG_zero]

  have F_0_h : F h = 0 := by
    dsimp[F,G,P,c]
    have hh5 : h^5 ≠ 0 := pow_ne_zero 5 (ne_of_gt hh)
    field_simp[hh5]
    ring

  have hf_cont : Continuous f := h_smooth.continuous

  have h_int_cont : Continuous
      (fun t : ℝ => ∫ x in (m - t)..(m + t), f x) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (deriv_int_symm f m t hf_cont).continuousAt

  have h_aux_cont : Continuous (simpsonAuxG f m) := by
    unfold simpsonAuxG
    exact h_int_cont.sub (by fun_prop)

  have hF_cont : ContinuousOn F (Set.Icc 0 h) := by
    have hF_continuous : Continuous F := by
      dsimp [F,G,P]
      exact h_aux_cont.sub (continuous_const.mul (continuous_pow 5))
    exact hF_continuous.continuousOn

  obtain ⟨ξ₁, hξ₁, F_1_1⟩ :=
    exists_deriv_eq_zero hh hF_cont (by rw [F_0_0, F_0_h])

  have hξ₁_closed : ξ₁ ∈ Set.Icc 0 h :=
    ⟨le_of_lt hξ₁.1, le_of_lt hξ₁.2⟩

  have hf1 : ContDiff ℝ 1 f := h_smooth.of_le (by norm_num)
  have hf2 : ContDiff ℝ 2 f := h_smooth.of_le (by norm_num)
  have hf_diff : Differentiable ℝ f := h_smooth.differentiable (by norm_num)
  have hdf : Differentiable ℝ (deriv f) := hf2.differentiable_deriv_two
  have hGdiff (t : ℝ) : DifferentiableAt ℝ G t := by
    change DifferentiableAt ℝ (simpsonAuxG f m) t
    unfold simpsonAuxG
    have h_integral_diff : DifferentiableAt ℝ
        (fun u : ℝ => ∫ x in (m - u)..(m + u), f x) t :=
      (deriv_int_symm f m t hf_cont).differentiableAt
    have h_term_diff : DifferentiableAt ℝ
        (fun u : ℝ => (u / 3) * (f (m - u) + 4 * f m + f (m + u))) t := by
      fun_prop
    exact h_integral_diff.sub h_term_diff

  have hPdiff (t : ℝ) : DifferentiableAt ℝ P t := by
    dsimp [P]
    fun_prop

  have hFderiv : deriv F = fun t => deriv G t - deriv P t := by
    funext t
    change deriv (G - P) t = deriv G t - deriv P t
    exact deriv_sub (hGdiff t) (hPdiff t)

  have hPderiv : deriv P = fun t => c * (5 * t ^ 4) := by
    funext t
    dsimp [P]
    rw [deriv_const_mul_field, deriv_pow_field]
    ring

  have hG1zero : deriv G 0 = 0 := by
    simpa only [G] using simpsonAuxG_deriv1_zero f m hf1

  have F_1_0 : deriv F 0 = 0 := by
    rw [hFderiv]
    change deriv G 0 - deriv P 0 = 0
    rw [hG1zero, hPderiv]
    norm_num

  have hP2zero : iteratedDeriv 2 P 0 = 0 := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num,
        iteratedDeriv_succ, iteratedDeriv_one, hPderiv]
    simp [deriv_const_mul_field]

  have hG2zero : iteratedDeriv 2 G 0 = 0 := by
    simpa only [G] using simpsonAuxG_deriv2_zero f m hf2

  have hGderiv_eq : deriv G =
      fun t => (2 / 3) * (f (m + t) + f (m - t) - 2 * f m) -
        (t / 3) * (deriv f (m + t) - deriv f (m - t)) := by
    funext t
    exact simpsonAuxG_deriv1 f m t hf1

  have hGderiv_diff : DifferentiableAt ℝ (deriv G) 0 := by
    rw [hGderiv_eq]
    fun_prop

  have hPderiv_diff : DifferentiableAt ℝ (deriv P) 0 := by
    rw [hPderiv]
    fun_prop

  have F_2_0 : iteratedDeriv 2 F 0 = 0 := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num,
        iteratedDeriv_succ, iteratedDeriv_one, hFderiv]
    change deriv (fun t => deriv G t - deriv P t) 0 = 0
    rw [← Pi.sub_def, deriv_sub hGderiv_diff hPderiv_diff]
    have hG2zero' : deriv (deriv G) 0 = 0 := by
      simpa only [show (2 : ℕ) = 1 + 1 by norm_num,
        iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hG2zero
    have hP2zero' : deriv (deriv P) 0 = 0 := by
      simpa only [show (2 : ℕ) = 1 + 1 by norm_num,
        iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hP2zero
    rw [hG2zero', hP2zero']
    norm_num
  have h_d1_aux_cont : Continuous (deriv (simpsonAuxG f m)) := by
    have hGderiv_cont : Continuous (deriv G) := by
      rw [hGderiv_eq]
      fun_prop
    simpa only [G] using hGderiv_cont

  have hPderiv_cont : Continuous (deriv P) := by
    rw [hPderiv]
    fun_prop

  have hF_d1_cont : ContinuousOn (deriv F) (Set.Icc 0 h) := by
    rw [hFderiv]
    exact (h_d1_aux_cont.sub hPderiv_cont).continuousOn

  have h_interval : Set.Icc 0 ξ₁ ⊆ Set.Icc 0 h := by
    intro x hx
    exact ⟨hx.1, le_trans hx.2 (le_of_lt hξ₁.2)⟩

  have hF_d1_cont' : ContinuousOn (deriv F) (Set.Icc 0 ξ₁) :=
    hF_d1_cont.mono h_interval

  have hξ₁_pos : 0 < ξ₁ := hξ₁.1

  obtain ⟨ξ₂, hξ₂, F_2_1⟩ :=
    exists_deriv_eq_zero hξ₁_pos hF_d1_cont' (by rw [F_1_0, F_1_1])

  have h_1_interval : Set.Icc 0 ξ₂ ⊆ Set.Icc 0 ξ₁ := by
    intro x hx
    exact ⟨hx.1, le_trans hx.2 (le_of_lt hξ₂.2)⟩

  have hGsecond_eq : iteratedDeriv 2 G =
      fun t => (1 / 3) * (deriv f (m + t) - deriv f (m - t)) -
        (t / 3) * (iteratedDeriv 2 f (m + t) + iteratedDeriv 2 f (m - t)) := by
    funext t
    exact simpsonAuxG_deriv2 f m t hf2

  have hdf2 : Differentiable ℝ (iteratedDeriv 2 f) :=
    h_smooth.differentiable_iteratedDeriv 2 (by norm_num)

  have hGsecond_cont : Continuous (iteratedDeriv 2 G) := by
    rw [hGsecond_eq]
    fun_prop

  have hPsecond_eq : iteratedDeriv 2 P =
      fun t => c * (20 * t ^ 3) := by
    funext t
    rw [show iteratedDeriv 2 P = deriv (deriv P) by
      ext x
      simp only [show (2 : ℕ) = 1 + 1 by norm_num,
        iteratedDeriv_succ, iteratedDeriv_zero]]
    rw [hPderiv]
    simp only [deriv_const_mul_field, deriv_pow_field]
    ring

  have hPsecond_cont : Continuous (iteratedDeriv 2 P) := by
    rw [hPsecond_eq]
    fun_prop

  have hGderiv_diff_all (t : ℝ) : DifferentiableAt ℝ (deriv G) t := by
    rw [hGderiv_eq]
    fun_prop

  have hPderiv_diff_all (t : ℝ) : DifferentiableAt ℝ (deriv P) t := by
    rw [hPderiv]
    fun_prop

  have hiter2 (g : ℝ → ℝ) :
      iteratedDeriv 2 g = deriv (deriv g) := by
    funext t
    simp only [show (2 : ℕ) = 1 + 1 by norm_num,
      iteratedDeriv_succ, iteratedDeriv_zero]

  have hFsecond_eq : iteratedDeriv 2 F =
      fun t => iteratedDeriv 2 G t - iteratedDeriv 2 P t := by
    funext t
    rw [hiter2 F, hiter2 G, hiter2 P, hFderiv]
    change deriv (fun u => deriv G u - deriv P u) t =
      deriv (deriv G) t - deriv (deriv P) t
    rw [← Pi.sub_def, deriv_sub (hGderiv_diff_all t) (hPderiv_diff_all t)]

  have hFsecond_cont : ContinuousOn (iteratedDeriv 2 F) (Set.Icc 0 h) := by
    rw [hFsecond_eq]
    exact (hGsecond_cont.sub hPsecond_cont).continuousOn

  have hξ₂_pos : 0 < ξ₂ := hξ₂.1
  have hFsecond_cont' : ContinuousOn (iteratedDeriv 2 F) (Set.Icc 0 ξ₂) :=
    hFsecond_cont.mono (h_1_interval.trans h_interval)

  have hF2ξ₂' : iteratedDeriv 2 F ξ₂ = 0 := by
    simpa only [hiter2] using F_2_1

  obtain ⟨ξ₃, hξ₃, F_3_0⟩ :=
    exists_deriv_eq_zero hξ₂_pos hFsecond_cont'
      (by rw [F_2_0, hF2ξ₂'])

  have hGsecond_diff_all (t : ℝ) : DifferentiableAt ℝ (iteratedDeriv 2 G) t := by
    rw [hGsecond_eq]
    fun_prop

  have hPsecond_diff_all (t : ℝ) : DifferentiableAt ℝ (iteratedDeriv 2 P) t := by
    rw [hPsecond_eq]
    fun_prop

  have hiter3 (g : ℝ → ℝ) :
      iteratedDeriv 3 g = deriv (iteratedDeriv 2 g) := by
    funext t
    simp only [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ]

  have hFthird_eq : iteratedDeriv 3 F =
      fun t => iteratedDeriv 3 G t - iteratedDeriv 3 P t := by
    funext t
    rw [hiter3 F, hiter3 G, hiter3 P, hFsecond_eq]
    change deriv (fun u => iteratedDeriv 2 G u - iteratedDeriv 2 P u) t =
      deriv (iteratedDeriv 2 G) t - deriv (iteratedDeriv 2 P) t
    rw [← Pi.sub_def, deriv_sub (hGsecond_diff_all t) (hPsecond_diff_all t)]

  have hPthird_eq : iteratedDeriv 3 P = fun t => c * (60 * t ^ 2) := by
    funext t
    rw [hiter3 P, hPsecond_eq]
    simp only [deriv_const_mul_field, deriv_pow_field]
    ring

  have hF3ξ₃ : iteratedDeriv 3 F ξ₃ = 0 := by
    simpa only [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ] using F_3_0

  have hF3_relation :
      -(ξ₃ / 3) *
          (iteratedDeriv 3 f (m + ξ₃) - iteratedDeriv 3 f (m - ξ₃)) -
        c * (60 * ξ₃ ^ 2) = 0 := by
    have hG3_at : iteratedDeriv 3 G ξ₃ =
        -(ξ₃ / 3) *
          (iteratedDeriv 3 f (m + ξ₃) - iteratedDeriv 3 f (m - ξ₃)) := by
      simpa only [G] using simpsonAuxG_deriv3 f m ξ₃ h_smooth
    rw [hFthird_eq, hPthird_eq] at hF3ξ₃
    change iteratedDeriv 3 G ξ₃ - c * (60 * ξ₃ ^ 2) = 0 at hF3ξ₃
    rw [hG3_at] at hF3ξ₃
    exact hF3ξ₃

  have hξ₃_pos : 0 < ξ₃ := hξ₃.1
  have hξ₃_lt_h : ξ₃ < h := by
    exact lt_trans hξ₃.2 (lt_trans hξ₂.2 hξ₁.2)

  have h_slope : ∃ ζ ∈ Set.Ioo (m - ξ₃) (m + ξ₃),
      iteratedDeriv 4 f ζ =
        (iteratedDeriv 3 f (m + ξ₃) - iteratedDeriv 3 f (m - ξ₃)) /
          ((m + ξ₃) - (m - ξ₃)) := by
    have hdf3 : Differentiable ℝ (iteratedDeriv 3 f) :=
      h_smooth.differentiable_iteratedDeriv 3 (by norm_num)
    obtain ⟨ζ, hζ, hζslope⟩ :=
      exists_deriv_eq_slope (iteratedDeriv 3 f)
        (show m - ξ₃ < m + ξ₃ by linarith)
        hdf3.continuous.continuousOn
        hdf3.differentiableOn
    refine ⟨ζ, hζ, ?_⟩
    rw [show iteratedDeriv 4 f = deriv (iteratedDeriv 3 f) by
      funext x
      simp only [show (4 : ℕ) = 3 + 1 by norm_num, iteratedDeriv_succ]]
    exact hζslope

  obtain ⟨ζ, hζ, hζ_slope⟩ := h_slope
  have hζ_mem : ζ ∈ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab.le]
    constructor
    · have hleft : a < m - ξ₃ := by rw [← h_left]; linarith
      exact le_trans (le_of_lt hleft) (le_of_lt hζ.1)
    · have hright : m + ξ₃ < b := by rw [← h_right]; linarith
      exact le_trans (le_of_lt hζ.2) (le_of_lt hright)

  have hcoef : c =
      - (iteratedDeriv 3 f (m + ξ₃) - iteratedDeriv 3 f (m - ξ₃)) /
        (180 * ξ₃) := by
    have hmul :
        c * (180 * ξ₃) =
          -(iteratedDeriv 3 f (m + ξ₃) - iteratedDeriv 3 f (m - ξ₃)) := by
      nlinarith [hF3_relation]
    have hden : 180 * ξ₃ ≠ 0 := ne_of_gt (mul_pos (by norm_num) hξ₃_pos)
    exact (eq_div_iff hden).2 (by nlinarith [hmul])

  have hcoef' : c = -(iteratedDeriv 4 f ζ) / 90 := by
    have hden : (m + ξ₃) - (m - ξ₃) = 2 * ξ₃ := by ring
    have hD :
        iteratedDeriv 3 f (m + ξ₃) - iteratedDeriv 3 f (m - ξ₃) =
          2 * ξ₃ * iteratedDeriv 4 f ζ := by
      have hslope : iteratedDeriv 4 f ζ =
          (iteratedDeriv 3 f (m + ξ₃) - iteratedDeriv 3 f (m - ξ₃)) /
            (2 * ξ₃) := by
        simpa [hden] using hζ_slope
      have hnonzero : 2 * ξ₃ ≠ 0 :=
        ne_of_gt (mul_pos (by norm_num) hξ₃_pos)
      field_simp [hnonzero] at hslope
      linarith
    rw [hD] at hcoef
    have hcancel : (2 * ξ₃) / (180 * ξ₃) = (1 : ℝ) / 90 := by
      field_simp [ne_of_gt hξ₃_pos]
      norm_num
    calc
      c = -(2 * ξ₃ * iteratedDeriv 4 f ζ) / (180 * ξ₃) := hcoef
      _ = -((2 * ξ₃) / (180 * ξ₃)) * iteratedDeriv 4 f ζ := by ring
      _ = -((1 : ℝ) / 90) * iteratedDeriv 4 f ζ := by rw [hcancel]
      _ = -(iteratedDeriv 4 f ζ) / 90 := by ring

  refine ⟨ζ, hζ_mem, ?_⟩
  change G h = -(h ^ 5 / 90) * iteratedDeriv 4 f ζ
  have hc : G h = c * h ^ 5 := by
    dsimp [c]
    have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 (ne_of_gt hh)
    exact (div_mul_cancel₀ (G h) hh5).symm
  rw [hc, hcoef']
  ring
