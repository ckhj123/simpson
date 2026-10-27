/-
## Main Proof of Simpson Error Estimation
Suppose that f ∈ C^4 (ℝ), and is a real-valued function.
Then ∃ ζ ∈ [a,b] such that
(∫ x in a..b, f x) - ((b - a) / 6) * (f a + 4 * f ((a + b) / 2) + f b) =
      - ((b - a) ^ 5 / 2880) * iteratedDeriv 4 f ζ



Note that [m-h,m+h] = [a,b], and we define the Auxiliary function as follows:

G:[0,h] → ℝ by

G(t)= ∫_{(m-t)}^{(m+t)} f(x)dx - t/3 (f(m-t) + 4 f(m) + f (m+t))

since t ∈ [0,h], [m-t,m+t] ⊆ [m-h,m+h] =[a,b]

So G is weill-defined on [0,h] also. Since f ∈ C^4([a,b]), f is continuous on [m-t,m+t]. hence ∫_{(m-t)}^{(m+t)} f(x)dx exists for all t ∈ [0,h].

by FTC, G ∈ C^4([0,h]) and G(h) = simpsonerror.




And then Consider the function F(t) = G(t) - (G(h)/h^5) * t^5, then F : [0,h] → ℝ also, and F ∈ C^4([0,h]).


And also that
G'(t) = 2/3 (f (m+t) + f(m-t) -2 f(m)) - t/3 (f'(m+t) - f'(m-t))
G''(t) = 1/3 (f'(m+t) - f'(m-t)) - t/3 (f''(m+t)+f''(m-t))
G'''(t) = -t/3 (f'''(m+t) - f'''(m-t))

and also  G(0)=G'(0)=G''(0)=0


So consider F(0) = G(0) - 0 * (G(h)/h^5) = 0  and F(h) = G(h)-G(h)=0.

Since F ∈ C^4[0,h], F derivative is continue at [0,h].
By Rolle'e Theorem, ∃ ζ₁ ∈ (0,h) such that F'(ζ₁)=0

Since F'(ζ₁)=0 and F'(0) = G'(0) - 0 * 5 * (G(h)/h^5) = 0 , and F' derivative is continue at [0,ζ₁].
By Rolle's Theorem, ∃ ζ₂ ∈ (0,ζ₁) such that F''(ζ₂)=0

Since F''(ζ₂)=0 and F''(0)=G''(0)-0 * 20 * (G(h)/h^5) =0, and F'' derivative is continue at [0,ζ₂].
By Rolle's Theorem, ∃ ζ₃ ∈ (0,ζ₂) such that F'''(ζ₃)=0



For F'''(ζ₃):

Since we have F'''(ζ₃)=G'''(ζ₃) - 60 * ζ₃^2 ((G(h)/h^5))

and G'''(ζ₃) = -ζ₃/3 (f'''(m+ζ₃) - f'''(m-ζ₃))

Since f''' ∈ C [a,b] where in particular 0< ζ₃ < ζ₂ < ζ₁ < h  , so f''' is continuous on [m-ζ₃,m+ζ₃] ⊆ [a,b]. And f^{(4)} is continuous at [m-ζ₃,m+ζ₃] ⊆ [a,b]. Then, by MVT, ∃ ζ ∈ [m-ζ₃,m+ζ₃] ⊆ [m-t,m+t] ⊆ [a,b] such that
f'''(m+ζ₃) - f'''(m-ζ₃) = 2 * ζ₃ * f^{(4)} (ζ)

So F'''(ζ₃)
= - ζ₃/3 *（2 * ζ₃ * f^{(4)} (ζ)）- 60 * ζ₃^2 ((G(h)/h^5))
=- 2/3 * ζ₃^2 * f^{(4)} (ζ) - 60 * ζ₃^2 (G(h)/h^5)

Since F'''(ζ₃) =0,
then we have - 2/3 * ζ₃^2 * f^{(4)} (ζ) = 60 * ζ₃^2 (G(h)/h^5)
G(h) = -1/90 * f^{(4)} (ζ) * h ^ 5


we get Error = -(b-a)^5/2880 * f^{(4)} (ζ) for some ζ ∈ [m-ζ₃,m+ζ₃] ⊆ [a,b]




==========================================================================
## Base and imports and open

-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open Polynomial
noncomputable section


private lemma integrable_term (c : ℝ) (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => c * x ^ n) MeasureTheory.volume a b := by
  exact (continuous_const.mul (continuous_pow n)).intervalIntegrable a b

--UseLess Lemma Now
private lemma integrable_term_one (c : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun x => c * x) MeasureTheory.volume a b :=
  (continuous_const.mul continuous_id).intervalIntegrable a b



/-
==========================================================================
## Basic Rule for SimpsonSum

lemma simpsonSum_add (f g : ℝ → ℝ) (a b : ℝ) and
lemma simpsonSum_smul (c : ℝ) (f : ℝ → ℝ) (a b : ℝ):

just develope the common associativity and communicativity on the simpson sum


==========================================================================
## Lemma eval_le_three


private lemma eval_le_three (p : ℝ[X]) (hp : p.natDegree ≤ 3) (x : ℝ)

Goal: To partite any polynomial of degree 3 into separate degree,
so to eliminate the degree sum each term for simpson sum,
to simplify the proof for exactness for simpson sum

## p.eval_eq_sum_range vs p.eval_eq_sum_range'
Note that rw[p.eval_eq_sum_range]
do not requires to supply a bound n : ℕ along side
with the proof of natDegree p < n while rw[p.eval_eq_sum_range'] does.


rw[p.eval_eq_sum_range]:
advantage on it can be applied to general polynomial for any degree = ∞ or finite degree, while


rw[p.eval_eq_sum_range'] requires finite bound n : ℕ with proof of p.natDegree < n.



-/


private lemma eval_le_three0 (p : ℝ[X]) (hp : p.natDegree ≤ 3) (x : ℝ) :
   p.eval x = p.coeff 0 * 1 + p.coeff 1 * x + p.coeff 2 * x^2 + p.coeff 3 * x^3 := by
   have h4 : p.natDegree < 4 := by omega
   rw[p.eval_eq_sum_range' h4]
   rw[Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ]
   ring

--vs

private lemma eval_le_three1 (p : ℝ[X]) (hp : p.natDegree ≤ 3) (x : ℝ) :
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

/-
=========================================================================
## Theorem 'simpson_exact_of_degree_le_three' (~40 → 17)




## prerequisite lemma
private lemma integrable_term (c : ℝ) (n : ℕ) (a b : ℝ) :
Goal: to show that each partit degree polynomial is indeed integrable



## main theorem change: integral_add to integral_finset_sum
Note that finding out using rw[intervalIntegral.integral_add ...]
is redundant and after carefullly searching the mathlib database,
it can be replaced by

rw [intervalIntegral.integral_finset_sum]



theorem intervalIntegral.integral_finset_sum {ι : Type*} (s : Finset ι)
    {f : ι → ℝ → E} (hf : ∀ i ∈ s, IntervalIntegrable (f i) μ a b) :


so using the same idea of proof in eval_le_three0,
we have succesfully reduced the code length from 20 line to 5 line
as stated below where 2 outcome / goal are the same
-/


def simpsonSum (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (b - a) / 6 * (f a + 4 * f ((a + b) / 2) + f b)
theorem simpson_exact_of_degree_le_three0 (p : ℝ[X]) (hp : p.natDegree ≤ 3) (a b : ℝ) :
    ∫ x in a..b, p.eval x = simpsonSum (fun x => p.eval x) a b := by
  have h4 : p.natDegree < 4 := by omega
  simp_rw [p.eval_eq_sum_range' h4]
  rw [intervalIntegral.integral_finsetSum]
  rw[Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ]
  ring_nf
  sorry
  --.... , which get the same result of the following in original code:

theorem simpson_exact_of_degree_le_three1 (p : ℝ[X]) (hp : p.natDegree ≤ 3) (a b : ℝ) :
    ∫ x in a..b, p.eval x = simpsonSum (fun x => p.eval x) a b := by
  simp_rw [eval_le_three0 p hp]
  have hi0 : IntervalIntegrable (fun x => p.coeff 0 * 1) MeasureTheory.volume a b :=
    integrable_term (p.coeff 0) 0 a b
  have hi1 : IntervalIntegrable (fun x => p.coeff 1 * x) MeasureTheory.volume a b :=
    integrable_term_one (p.coeff 1) a b
  have hi2 : IntervalIntegrable (fun x => p.coeff 2 * x^2) MeasureTheory.volume a b :=
    integrable_term (p.coeff 2) 2 a b
  have hi3 : IntervalIntegrable (fun x => p.coeff 3 * x^3) MeasureTheory.volume a b :=
    integrable_term (p.coeff 3) 3 a b
  have hi01 : IntervalIntegrable
      (fun x => p.coeff 0 * 1 + p.coeff 1 * x) MeasureTheory.volume a b :=
    hi0.add hi1
  have hi012 : IntervalIntegrable
      (fun x => p.coeff 0 * 1 + p.coeff 1 * x + p.coeff 2 * x^2) MeasureTheory.volume a b :=
    hi01.add hi2
  rw [intervalIntegral.integral_add hi012 hi3]
  rw [intervalIntegral.integral_add hi01 hi2]
  rw [intervalIntegral.integral_add hi0 hi1]
  sorry

/--

## elimination of lemma eval_le_three0/1
Note that using the new verison and get the idea from then eval_le_three0/1 is useless in this context, hence deleted in the main code

## details in change after applying 'finsetSum'

after the line rw[intervalIntegral.integral_finsetSum], it split into 2 goal, hence using the · to separate into 2 goal, where the later goal shows integrability by the exact (continuous_const.mul (continuous_pow i)).intervalIntegrable a b. Note that the lemma

private lemma integrable_term (c : ℝ) (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => c * x ^ n) MeasureTheory.volume a b


private lemma integrable_term_one (c : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun x => c * x) MeasureTheory.volume a b

are also no longer in used as we do not need to deal with the case of c x vs c x ^1 as Finset.sum approach treats all term uniformly as c_i x^i.

However, i prefer using
· intro i _
    exact integrable_term (p.coeff i) i a b

to make things simple.


## Finset property
For reducing the Finset, AI is asked for its property:

Finset.sum_range_succ : peels off highest term resp.
e.g. ∑ range.4 f(i) = ∑ range.3 f(i) + f(4).
Hence repeatedly → (((range 0) + f(0)) + f(1)) + f(2) + f(3).

Finset.range_zero : range 0 = ∅
Converts sum over (range 0) into sum over ∅.

Converts sum over (range 0) into sum over ∅.
Rewrite sum over ∅ to 0, hence use with Finset.range_zero
to peel make range 0 = 0

zero_add
to make range 0 + f(0) + f(1) + f(2) + f(3) = 0 +f(0) + f(1)) + f(2) + f(3)
 to f(0) + f(1) + f(2) + f(3)

Finally pow_zero, pow_one to rule x^0=1 and x^1=x

=========================================================================

## Simpson Rules.

General definition.
-/
private def simpsonAuxG (f : ℝ → ℝ) (m : ℝ) (t : ℝ) : ℝ :=
  (∫ x in (m - t)..(m + t), f x) - (t / 3) * (f (m - t) + 4 * f m + f (m + t))


/-








First, we shift our focus to the first lemma: the FTC deriv_int_lemma


## deriv_int_lemma (85 → 21)
-/
private lemma deriv_int_symm (f : ℝ → ℝ) (m t : ℝ) (hf : Continuous f) :
    HasDerivAt (fun t => ∫ x in (m-t)..(m+t), f x)
      (f (m + t) + f (m - t)) t :=  by


/-
Note the original approach is to do
1: split the integral from ∫ _{m-t}^{m+t} fx into ∫_m^{m+t} f x - ∫ _m^{m-t} f x
2: apply FTC by intervalIntegral.integral_hasDerivAt_right
on HasDerivAt (fun (u : ℝ) => ∫ (x : ℝ) in a..u, f x) (f b) b
3: need to deal with chain rule for each function f(m+t), f(m-t)
4: hence each function need at least 2 'have'  statement, totally of 4 'have' statements


to make things better, first lets separate the original proof into 3 parts:

-/
--1: Separate integral into 2 parts to apply for FTC:
  have h_split : (fun t => ∫ x in (m-t)..(m + t) , f x) =
                 (fun t => (∫ x in m..(m+t), f x)- (∫ x in m..(m-t), f x))  := by
    ext u
    have h1 : IntervalIntegrable f MeasureTheory.volume (m - u) m := hf.intervalIntegrable _ _
    have h2 : IntervalIntegrable f MeasureTheory.volume m (m + u) := hf.intervalIntegrable _ _
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
    rw [intervalIntegral.integral_symm (m-u) m]
    ring
  rw [h_split]

/-
## Part 3: splitting ∫_{m-t}^{m+t} into ∫_m^{m+t} - ∫_m^{m-t}



Notice that the step
1: we need extra lemma to show that the
∫_m^{m+t} and ∫_m^{m-t} are integrable
2:  use integral_symm (m-u) m to switch the bound of integral and ring
3: use integral_add_adjacent_intervals to add the bound together by h1,h2

To optimize,

1: on step 2, we conbind the ring and the symm into 1 rw:
rw[integral_symm (m-u) m , sub_neg_eq_add] to convert the -- ∫ to + ∫
2: the extra lemma can be put into integral_add_adjacent_intervals directly by providing that
 hf.intervalIntegrable _ _ using continuity. and with .symm at end (BY AI)

 where intervalIntegral.integral_add_adjacent_intervals:
 theorem integral_add_adjacent_intervals
  (hab : IntervalIntegrable f μ a b)
  (hbc : IntervalIntegrable f μ b c) :
  ((∫ x in a..b, f x ∂μ) + ∫ x in b..c, f x ∂μ) = ∫ x in a..c, f x ∂μ

  requires hab, hbc to be integrable, which can be proven by cont. directly.


Problem: hf.intervalIntegrable _ _ lean doesn't know which measure you are integrating w.r.t
when having _ _ leaves blank. Lean leaves the measure as an unconstrained metavariable.

So explicitly state m (m-u) and also  m (m+u) to solve the issue.

-/
-- The Right part
  have h_right_base : HasDerivAt (fun u => ∫ x in m..u, f x) (f (m + t)) (m + t) := by
    exact intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable m (m + t))
      (hf.stronglyMeasurableAtFilter MeasureTheory.volume (nhds (m + t)))
      hf.continuousAt
  have h_shift_right : HasDerivAt (fun t => m + t) 1 t := (hasDerivAt_id t).const_add m
  have h_right : HasDerivAt (fun t => ∫ x in m..(m + t), f x) (f (m + t)) t := by
    convert h_right_base.comp t h_shift_right using 1
    · funext u
      rfl
    · ring
-- And the Left Part
  have h_left_base : HasDerivAt (fun u => ∫ x in m..u, f x) (f (m - t)) (m - t) := by
    exact intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable m (m - t))
      (hf.stronglyMeasurableAtFilter MeasureTheory.volume (nhds (m - t)))
      (hf.continuousAt)
  have h_shift_left : HasDerivAt (fun t => m - t) (-1) t := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      ((hasDerivAt_id t).neg.const_add m)
  have h_left : HasDerivAt (fun t => ∫ x in m..(m - t), f x) (-f (m - t)) t := by
    convert h_left_base.comp t h_shift_left using 1
    · funext u
      rfl
    · ring


--Notice that the above is duplicated when applying the FTC, where we do the same step 2 times.
/-
## Part 1: FTC
To reduce the duplicated part, we shall apply FTC on arbitrary function, then call it out by using
 : intervalIntegral.integral_hasDerivAt_right:

 theorem intervalIntegral.integral_hasDerivAt_right
    {E : Type u_3} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {a b : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hmeas : StronglyMeasurableAtFilter f (nhds b) MeasureTheory.volume)
    (hb : ContinuousAt f b) :
    HasDerivAt (fun (u : ℝ) => ∫ (x : ℝ) in a..u, f x) (f b) b

where
hf is given by (hf.intervalIntegrable _ _) (AI)
hmeas is given by (hf.stronglyMeasurableAtFilter _ _) (AI)
hb is given by (hf : Continuous f)

a function that is continuous everywhere
is automatically well-behaved enough to be measurable and
integrable over any bounded interval. (Online search + AI assist to implant this)

have h_FTC (u : ℝ) : HasDerivAt (fun s => ∫ x in m..s, f x) (f u) u :=
    intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable _ _ )
      (hf.stronglyMeasurableAtFilter _ _ )
      hf.continuousAt

-/

/-
## Part 2: Left and Right

have hR : HasDerivAt (fun t => ∫ x in m..(m + t), f x) (f (m + t)) t

have hL : HasDerivAt (fun t => ∫ x in m.. (m - t) , f x) (-f (m - t)) t


simpa using e
simplifies both the current goal and the expression e,
 and then attempts to close the goal
 by matching the simplified version of e with the simplified goal.

 we use simpa to apply chain rule and simplifies
 f(m+t) · 1 → f(m+t) a and f(m-t) · (-1) → - f(m -t)

 Note that by
 theorem HasFDerivAt.comp (x : E) (hg : HasFDerivAt g g' (f x))
 (hf : HasFDerivAt f f' x) :
  HasFDerivAt (g ∘ f) (g'.comp f') x

to use simpa for composition rule,
simpa using hg.comp x hf
we need to guarantee the hg and hf, which

For hR:
hg.comp corresp. to (h_FTC (m+t)).comp,
and hf corresp. to ((hasDerivAt_id t).const_add m)

For hL:
hg.comp corresp. to (h_FTC (m-t)).comp,
and hf corresp. to ((hasDerivAt_id t).neg.const_add m)

Hence the Left and Right part have succesfully reduced from 20 line to 2 line

-/
  have h_total : HasDerivAt
      (fun t => (∫ x in m..(m + t), f x) - (∫ x in m..(m - t), f x))
      (f (m + t) + f (m - t)) t := by
    convert h_right.sub h_left using 1
    ring
  simpa using h_total

/-
Finally use convert to write  HasDerivAt.sub hR hL using hR.sub h.L

=========================================================================

## lemma simpsonAuxG_deriv1 (64 → 8)





-/
private lemma simpsonAuxG_deriv1 (f : ℝ → ℝ) (m t : ℝ) (hf : ContDiff ℝ 1 f) :
    deriv (simpsonAuxG f m) t =
      (2 / 3) * (f (m + t) + f (m - t) - 2 * f m) -
      (t / 3) * (deriv f (m + t) - deriv f (m - t)) := by

--Our main goal is to reduce the proof by using HasDeriv and its d-rule

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

/-
note that the step of proof above can be partitioned into steps:
1: define the cont and deriv of the function
2:find the deriv of ∫ x in (m-t)..(m+t), f x
3: find the deriv of (t / 3) * (f (m - t) + 4 * f m + f (m + t))
which is separated into subgoal of
3.1 : both deriv is differentiable
3.2 : deriv of f(m-t)
3.3 : deriv of f(m+t)
3.4 : deriv of f(m-t) + 4 * f(m)
3.5 : combind 3.3, 3.4

However, using the idea from the deriv_int_symm lemma, where we can pack things into 1 line of code,
 and with the help of AI, i have learnt that we can change differentiability → derivative

1: since hf : ContDiff ℝ 1 f, define hd : Differentiable ℝ f

Since Differentiable ℝ f ≅ ∀ x : ℝ , DifferentiableAt ℝ f x
and hd is a func taking pt x as an argument, hd(m+t) means a func. taking pt. (m+t)
So hd (m+t) : proof of DifferentiableAt ℝ f (m + t)

2: Connect Differentiability to Derivative:

DifferentiableAt.hasDerivAt turns a general differentiability statement into a HasDerivAt statement using the deriv operator:

e.g. (hd (m + t)).hasDerivAt → HasDerivAt f (deriv f (m + t)) (m + t)

3: then we apply chain rule (HasDerivAt.comp) : where outer function is f, inner is (m+t)

(hd (m + t)).hasDerivAt.comp t ((hasDerivAt_id t).const_add m)

where outer function proof is (hd (m + t)).hasDerivAt
inner function proof is (hasDerivAt_id t).const_add m

Combining them with .comp t tells Lean to compose the two derivatives at point t: Derivative = deriv f(m + t) · 1 = deriv f(m + t)

Hence we have the line of code:
have h1 := (hd (m + t)).hasDerivAt.comp t ((hasDerivAt_id t).const_add m)

Similarly,

have h2 := (hd (m - t)).hasDerivAt.comp t ((hasDerivAr_id t).neg.const_add m)

To deal with additivity, we use h1.add h2 for HasDerivAt.add h1 h2

have h3 := (h2.add (hasDerivAt_const t (4 * f (m)))).add h1

have h_prod := ((hasDerivAt_id t).div_const 3).mul h_sum


we left with

have hd : Differentiable ℝ f:= hf.differentiable (by simp)
have hp := (hd (m + t)).hasDerivAt.comp t ((hasDerivAt_id t).const_add m)
have hm := (hd (m - t)).hasDerivAt.comp t ((hasDerivAt_id t).neg.const_add m)  have hc := ((hp.add hm).sub (hasDerivAt_const t (2 * f m))).const_mul (2/3)
have hb := ((hasDerivAt_id t).div_const 3).mul (deriv2_symm f m t hf)
have hd : deriv (simpsonAuxG f m) =
    (fun y => (2 / 3) * (f (m + y) + f (m - y) - 2 * f m)) -
    ((fun x => id x / 3) * (fun s => deriv f (m + s) - deriv f (m - s))) := by
  funext s
  exact simpsonAuxG_deriv1 f m s (hf.of_le (by norm_num))



-/
