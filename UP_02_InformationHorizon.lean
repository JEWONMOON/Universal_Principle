import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open Real Topology

namespace SingularityPrinciple.Horizon

-- 정보 채널 또는 진공의 스펙트럼 (고유값 수열).
variable (spectrum : ℕ → ℝ)

-- [물리적 공리 1] 정보 지평 (Information Horizon)
class HasInformationHorizon (spectrum : ℕ → ℝ) : Prop where
  exponential_decay : ∃ (C α : ℝ), C > 0 ∧ α > 0 ∧ 
    ∀ n, spectrum n ≤ C * exp (-α * (n : ℝ))

-- 대각합-클래스 (Trace-class / Nuclearity)
def IsTraceClass (spectrum : ℕ → ℝ) : Prop :=
  Summable spectrum

-- [핵성 유도 정리] Fundamental Theorem of Horizon-to-Nuclearity
theorem nuclearity_of_information_horizon (spectrum : ℕ → ℝ)
    [H : HasInformationHorizon spectrum]
    (h_pos : ∀ n, 0 ≤ spectrum n) : 
    IsTraceClass spectrum := by
  -- 1. 정보 지평 공리로부터 상수 추출
  rcases H.exponential_decay with ⟨C, α, hC, hα, h_bound⟩
  
  -- 2. 비교 판정법을 위한 식 정리
  have h_comparison : ∀ n, spectrum n ≤ C * (exp (-α)) ^ n := by
    intro n
    -- [마지막 sorry 해결 완료] 지수 법칙 증명 
    have h_exp : exp (-α * (n : ℝ)) = (exp (-α)) ^ n := by
      -- 교환 법칙으로 순서를 바꾸고 ( -α * n -> n * -α )
      rw [mul_comm (-α) (n : ℝ)]
      -- Mathlib의 실수-자연수 지수 정리 적용
      exact Real.exp_nat_mul (-α) n
      
    have h_b := h_bound n
    rw [h_exp] at h_b
    exact h_b
    
  -- 3. 기하급수 수렴성 증명
  -- α > 0 이므로 -α < 0 임을 명시적으로 변환
  have h_neg_alpha : -α < 0 := neg_lt_zero.mpr hα
  have h_geom_ratio : exp (-α) < 1 := exp_lt_one_iff.mpr h_neg_alpha
  have h_geom_pos : 0 ≤ exp (-α) := (exp_pos (-α)).le
  
  -- 공비가 1보다 작은 기하급수는 수렴한다
  have h_geom_summable : Summable (fun n => C * (exp (-α)) ^ n) := by
    apply Summable.mul_left
    exact summable_geometric_of_lt_one h_geom_pos h_geom_ratio
    
  -- 4. 비교 판정법 적용
  exact Summable.of_nonneg_of_le h_pos h_comparison h_geom_summable

end SingularityPrinciple.Horizon
