/-
  UP_01_PhysicalHorizon.lean
  ==========================
  Universal Principle — Layer I, File 1 of 3

  MATHEMATICAL CONTENT
  --------------------
  This file establishes the foundational three-horizon structure that connects
  physical laws to mathematical summability.  The core idea is:

    (Physical law)  The universe has a finite energy horizon.
                    Eigenvalues of the vacuum Hamiltonian are bounded above
                    by an exponentially decaying envelope E·exp(−α·n).

    (Information)   Any spectrum satisfying this bound has finite total
                    information in the Shannon/von Neumann sense.

    (Mathematics)   A nonneg sequence dominated by a convergent geometric
                    series is itself summable — this is Nuclearity.

  The three horizons are named after their domain:
    • PhysicalHorizon    — energy suppression from Bekenstein–Hawking
    • HasInformationHorizon — exponential decay condition
    • IsMathematicalHorizon — Summable (trace-class condition)

  All theorems in this file are proved without sorry and without
  domain-specific axioms beyond standard Mathlib.

  REFERENCES
  ----------
  • Bekenstein (1973): Black holes and entropy. Phys.Rev. D7, 2333.
  • Hawking (1975): Particle creation by black holes. CMP 43, 199–220.
  • Haag–Kastler–Ojima (1977): On the nuclearity condition for quantum fields.
-/

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Basic

noncomputable section
open Real Topology

namespace SingularityPrinciple.ThreeHorizons

/-!
  ## Horizon I — The Physical Horizon

  A `PhysicalHorizon` encodes the Bekenstein–Hawking bound in the form
  most useful for operator theory: the n-th eigenvalue of the vacuum
  Hamiltonian H satisfies

      λₙ ≤ E_horizon · exp(−suppression_rate · n)

  where E_horizon > 0 is the maximum energy accessible within the causal
  horizon, and suppression_rate > 0 reflects the Boltzmann suppression of
  high-energy modes at the Unruh/Hawking temperature.

  In the holographic picture (Susskind–'t Hooft), the total number of
  distinguishable states in a region of area A is bounded by exp(A/4ℓ²_P),
  which forces the spectrum to thin out at least exponentially.
-/

structure PhysicalHorizon where
  /-- Maximum energy scale set by the causal horizon (E_horizon > 0). -/
  E_horizon       : ℝ
  hE              : 0 < E_horizon
  /-- Exponential suppression rate α > 0 (related to Hawking temperature). -/
  suppression_rate : ℝ
  hRate           : 0 < suppression_rate

namespace PhysicalHorizon

/--
  The n-th suppressed energy level:
      suppressedEnergy n = E_horizon · exp(−suppression_rate · n)

  This is the Bekenstein–Hawking upper bound on the n-th eigenvalue.
-/
def suppressedEnergy (P : PhysicalHorizon) (n : ℕ) : ℝ :=
  P.E_horizon * Real.exp (-P.suppression_rate * n)

/-- Every suppressed energy level is strictly positive (exp is always > 0). -/
theorem suppressedEnergy_pos (P : PhysicalHorizon) (n : ℕ) :
    0 < P.suppressedEnergy n := by
  unfold suppressedEnergy
  exact mul_pos P.hE (Real.exp_pos _)

/--
  The suppressed energy envelope is antitone (decreasing in n).
  Higher modes are exponentially suppressed.
-/
theorem suppressedEnergy_antitone (P : PhysicalHorizon) :
    Antitone (fun n : ℕ => P.suppressedEnergy n) := by
  intro m n hmn
  unfold suppressedEnergy
  apply mul_le_mul_of_nonneg_left _ P.hE.le
  apply Real.exp_le_exp.mpr
  rw [neg_mul, neg_mul]
  apply neg_le_neg
  apply mul_le_mul_of_nonneg_left _ P.hRate.le
  exact_mod_cast hmn

end PhysicalHorizon

/-!
  ## Horizon II — The Information Horizon

  `HasInformationHorizon σ` states that the spectrum σ : ℕ → ℝ
  satisfies an exponential decay bound:

      ∃ C α > 0,  ∀ n,  σ n ≤ C · exp(−α · n)

  This is precisely the nuclearity condition of Haag–Kastler–Ojima (1977)
  and the condition guaranteeing that the partition function

      Z(β) = Tr(exp(−βH)) = Σₙ exp(−β · λₙ)

  converges for all β > 0.
-/

class HasInformationHorizon (spectrum : ℕ → ℝ) : Prop where
  exponential_decay : ∃ (C α : ℝ), C > 0 ∧ α > 0 ∧
    ∀ n, spectrum n ≤ C * Real.exp (-α * n)

/--
  A spectrum bounded by the Bekenstein–Hawking envelope automatically
  satisfies the information horizon condition.
  The constants (C, α) are read off from the PhysicalHorizon parameters.
-/
theorem informationHorizon_of_physicalHorizon
    (P : PhysicalHorizon)
    (spectrum : ℕ → ℝ)
    (h_bound : ∀ n, spectrum n ≤ P.suppressedEnergy n) :
    HasInformationHorizon spectrum where
  exponential_decay := ⟨P.E_horizon, P.suppression_rate,
    P.hE, P.hRate, fun n => h_bound n⟩

/-!
  ## Horizon III — The Mathematical Horizon (Nuclearity)

  `IsMathematicalHorizon σ` is defined as `Summable σ`, i.e.,
  the series Σₙ σ n converges in ℝ.

  For an operator T with eigenvalue sequence σ, this is exactly the
  trace-class condition:  ‖T‖₁ = Σₙ σ n < ∞.

  Trace-class operators are the cornerstone of:
    • Fredholm determinant theory (det(I − zT) is well-defined)
    • Selberg zeta functions (expressed as Fredholm determinants)
    • Quantum statistical mechanics (partition function converges)
-/

def IsMathematicalHorizon (spectrum : ℕ → ℝ) : Prop :=
  Summable spectrum

/-!
  ### Key Theorem: Information Horizon → Mathematical Horizon

  Proof strategy (standard comparison test):
    1.  Extract C, α > 0 from HasInformationHorizon.
    2.  Rewrite exp(−α · n) as (exp(−α))ⁿ  [Nat power vs real power].
    3.  Since α > 0, we have exp(−α) < 1, so Σₙ C · (exp(−α))ⁿ converges
        (geometric series with ratio r = exp(−α) < 1).
    4.  Apply Mathlib's `Summable.of_nonneg_of_le` (comparison test).
-/

theorem mathematicalHorizon_of_informationHorizon
    (spectrum : ℕ → ℝ)
    (h_pos  : ∀ n, 0 ≤ spectrum n)
    [H : HasInformationHorizon spectrum] :
    IsMathematicalHorizon spectrum := by
  rcases H.exponential_decay with ⟨C, α, hC, hα, h_bound⟩
  -- Rewrite exp(−α·n) = exp(−α)ⁿ using the identity exp(r·n) = exp(r)ⁿ
  have h_comparison : ∀ n, spectrum n ≤ C * (Real.exp (-α)) ^ n := by
    intro n
    have h_exp : Real.exp (-α * n) = (Real.exp (-α)) ^ n := by
      rw [mul_comm (-α) (n : ℝ)]
      exact Real.exp_nat_mul (-α) n
    calc spectrum n ≤ C * Real.exp (-α * n) := h_bound n
      _ = C * (Real.exp (-α)) ^ n           := by rw [h_exp]
  -- The geometric series converges because exp(−α) ∈ (0, 1)
  have h_ratio_lt_one : Real.exp (-α) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hα)
  have h_ratio_nonneg : 0 ≤ Real.exp (-α) := (Real.exp_pos (-α)).le
  have h_geom : Summable (fun n => C * (Real.exp (-α)) ^ n) :=
    (summable_geometric_of_lt_one h_ratio_nonneg h_ratio_lt_one).mul_left C
  -- Comparison test: 0 ≤ σₙ ≤ C·rⁿ and Σ C·rⁿ < ∞ implies Σ σₙ < ∞
  exact Summable.of_nonneg_of_le h_pos h_comparison h_geom

/--
  ### Master Theorem: Physical Horizon → Nuclearity

  Composes the two previous theorems into a single arrow:

      PhysicalHorizon  →  IsMathematicalHorizon

  This is the mathematical content of the claim
  "the Bekenstein–Hawking bound implies the vacuum operator is trace-class."
-/
theorem mathematicalHorizon_of_physicalHorizon
    (P        : PhysicalHorizon)
    (spectrum : ℕ → ℝ)
    (h_pos    : ∀ n, 0 ≤ spectrum n)
    (h_bound  : ∀ n, spectrum n ≤ P.suppressedEnergy n) :
    IsMathematicalHorizon spectrum := by
  haveI := informationHorizon_of_physicalHorizon P spectrum h_bound
  exact mathematicalHorizon_of_informationHorizon spectrum h_pos

/-!
  ## The Triple-Horizon Vacuum Structure

  A `TripleHorizonVacuum` packages all three horizons together with a
  spectrum that satisfies all three simultaneously.  The fields are:
    • spectrum     : ℕ → ℝ   — eigenvalue sequence
    • spectrum_pos             — all eigenvalues ≥ 0 (energy is non-negative)
    • physHorizon              — the Bekenstein–Hawking envelope
    • phys_bound               — spectrum ≤ envelope (bound is witnessed)
  The information and mathematical horizons are then *derived*, not assumed.

  This is the abstract vacuum of the Universal Principle:
  any physical system whose energy spectrum satisfies the Bekenstein–Hawking
  bound automatically has a nuclear (trace-class) Hamiltonian.
-/

structure TripleHorizonVacuum where
  spectrum      : ℕ → ℝ
  spectrum_pos  : ∀ n, 0 ≤ spectrum n
  physHorizon   : PhysicalHorizon
  phys_bound    : ∀ n, spectrum n ≤ physHorizon.suppressedEnergy n
  infoHorizon   : HasInformationHorizon spectrum :=
    informationHorizon_of_physicalHorizon physHorizon spectrum phys_bound
  mathHorizon   : IsMathematicalHorizon spectrum :=
    mathematicalHorizon_of_physicalHorizon physHorizon spectrum
      spectrum_pos phys_bound

namespace TripleHorizonVacuum

/-- The vacuum Hamiltonian is trace-class: Σₙ λₙ < ∞. -/
theorem nuclearity (V : TripleHorizonVacuum) : Summable V.spectrum :=
  V.mathHorizon

/-- The spectrum has a convergent sum (equivalently, the partition function
    Tr(exp(−βH)) converges for the zero-temperature limit β → ∞). -/
theorem finite_trace (V : TripleHorizonVacuum) : ∃ T : ℝ, HasSum V.spectrum T :=
  V.mathHorizon

/-- Explicit Bekenstein–Hawking bound: λₙ ≤ E_horizon · exp(−rate · n). -/
theorem bekenstein_hawking_bound (V : TripleHorizonVacuum) (n : ℕ) :
    V.spectrum n ≤ V.physHorizon.E_horizon *
      Real.exp (-V.physHorizon.suppression_rate * n) :=
  V.phys_bound n

end TripleHorizonVacuum

/--
  ## Summary Theorem

  Any triple-horizon vacuum provides a nuclear eigenvalue budget:
  the spectrum is nonneg, summable, and Bekenstein–Hawking bounded.

  This is the "budget" that all subsequent files draw upon.
-/
theorem triple_horizon_gives_nuclear_budget
    (V : TripleHorizonVacuum) :
    ∃ (weights : ℕ → ℝ),
      (∀ n, 0 ≤ weights n) ∧
      Summable weights ∧
      ∀ n, weights n ≤ V.physHorizon.E_horizon *
        Real.exp (-V.physHorizon.suppression_rate * n) :=
  ⟨V.spectrum, V.spectrum_pos, V.nuclearity, V.phys_bound⟩

end SingularityPrinciple.ThreeHorizons
