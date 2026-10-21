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
## Theorem 'simpson_exact_of_degree_le_three'




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
-/
