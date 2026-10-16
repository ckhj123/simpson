> **WORK IN PROGRESS / DRAFT**  
> This repository is actively updated with formal Lean 4 proof code, tactic files, and documentation for my contribution to Mathlib4.

# Formalization of Simpson's Rule in Lean 4

This repository contains the Lean 4 source code, tactic states, and formal proof documentation for the numerical integration bounds of Simpson's Rule, aimed at contributing to `mathlib4` (the mathematical library for Lean 4).

## Author & Project Context
- **Author:** Chan Kwan Ho, Jason
- **Role:** Independent Formalizer / Open-Source Contributor
- **Department:** Department of Mathematics, The Chinese University of Hong Kong (CUHK)
- **Target Repository:** [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4)

## Research Manuscripts & Documentation
- [ View Lean 4 Code File (`SimpsonRule.lean`)](SimpsonRule.lean) *(Active Draft)*

## Key Research Scope & Theoretical Highlights
- **Synthetic Formalization of Numerical Integration:** Constructing explicit proof objects in Lean 4 to establish error bounds and convergence rates for composite Simpson's Rule.
- **Calculus & Measure Theory Integration:** Navigating Mathlib's measure-theoretic integration framework (`MeasureTheory.integral`) and differential calculus bounds within Lean's deterministic kernel.
- **AI-Assisted Tactic Workflow:** Leveraging LLM-guided tactic suggestion alongside Lean 4 interactive state visualization to optimize macro structures and resolve complex type-mismatch constraints across dependent types.

## Target Mathlib Contribution Scope
- **Domain:** Analysis / Numerical Analysis / Integration Bounds
- **Goal:** Provide a verified, reusable formalization of Simpson's Rule error estimation for the broader Lean theorem-proving community.

## Key References
- [1] Leonardo de Moura and Sebastian Ullrich. "The Lean 4 Theorem Prover and Programming Language." In: *Automated Deduction – CADE 28* (2021), pp. 625–635.
- [2] Lean Community. *Mathematics in Lean*. URL: https://leanprover-community.github.io/mathematics_in_lean/.
- [3] Another book
- [4] Math3230 2526 Notes by Prof. Jun Zou CUHK
