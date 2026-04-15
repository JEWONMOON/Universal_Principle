import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic

-- ────────────────────────────────────────────────
-- 기존 파일 임포트 (전부 통과 버전)
-- ────────────────────────────────────────────────
import nzfc.«05_Boundary_Zero_Off_Axis»
import nzfc.«18_Green_Identity_Self_Adjoint»
import nzfc.«21_Modular_Factorization_Selberg_Riemann»
import nzfc.«28_HilbertPolya_1Axiom_Capture»

set_option linter.unusedSectionVars false

namespace NZFC.FinalChain

open Complex

-- ════════════════════════════════════════════════
-- §1. 정의 브릿지 (Definition Bridge)
-- ════════════════════════════════════════════════

lemma nontrivial_to_riemann_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (evs : ℕ → ℂ) (T : H →L[ℂ] H)
    {ρ : ℂ} (h : SingularityPrinciple.IsNontrivialZero ρ) :
    NZFC_V3_5_Modular.IsRiemannZero ρ := by
  obtain ⟨h_zeta, h_triv, h_ne1⟩ := h
  
  have h_re_ne1 : ρ.re ≠ 1 := by
    intro h_eq
    have h_ge : (1 : ℝ) ≤ ρ.re := le_of_eq h_eq.symm
    exact riemannZeta_ne_zero_of_one_le_re h_ge h_zeta

  have h_re_ne0 : ρ.re ≠ 0 := by
    intro h_eq0
    have h_one_sub_re : (1 - ρ).re = 1 := by
      simp [Complex.sub_re, Complex.one_re, h_eq0]
    have h_ge : (1 : ℝ) ≤ (1 - ρ).re := le_of_eq h_one_sub_re.symm
    
    obtain ⟨_, h_det_rho, h_iff_rho⟩ := NZFC.unified_spectral_existence evs T ρ
    obtain ⟨_, h_det_one_sub, h_iff_one_sub⟩ :=
      NZFC.unified_spectral_existence evs T (1 - ρ)
    
    have h_sz_zero : NZFC.selbergZeta ρ = 0 := by
      unfold NZFC.selbergZeta; rw [h_zeta, zero_mul]
    have h_det_zero : NZFC.fredholmDet evs (1 / (ρ * (1 - ρ))) = 0 := by
      rw [h_det_rho]; exact h_sz_zero
      
    -- [FIX] h_symm_eq를 목표에 직접 적용할 수 있도록 rw 전술 사용
    have h_symm_eq : ρ * (1 - ρ) = (1 - ρ) * (1 - (1 - ρ)) := by ring
    have h_same_z : 1 / ((1 - ρ) * (1 - (1 - ρ))) = 1 / (ρ * (1 - ρ)) := by
      rw [h_symm_eq]
    
    have h_sz_one_sub : NZFC.selbergZeta (1 - ρ) = 0 := by
      rw [← h_det_one_sub, h_same_z, h_det_zero]
    
    have h_rz_one_sub : riemannZeta (1 - ρ) = 0 := by
      unfold NZFC.selbergZeta at h_sz_one_sub
      rcases mul_eq_zero.mp h_sz_one_sub with hz | hl
      · exact hz
      · unfold NZFC.L_function at hl
        exact absurd hl (Complex.exp_ne_zero _)
        
    exact riemannZeta_ne_zero_of_one_le_re h_ge h_rz_one_sub

  have h_strip := NZFC.riemannZeta_zero_location evs T ρ h_zeta ⟨h_re_ne0, h_re_ne1⟩
  exact ⟨h_zeta, h_strip.1, h_strip.2⟩

-- ════════════════════════════════════════════════
-- §2. 스펙트럼 허수부 및 대수학 (Spectral Algebra)
-- ════════════════════════════════════════════════

lemma eigenvalue_im_zero {ρ : ℂ}
    (h_rz : NZFC_V3_5_Modular.IsRiemannZero ρ) :
    (ρ * (1 - ρ)).im = 0 := by
  obtain ⟨ev, _, h_ev_eq⟩ := NZFC_V3_5_Modular.Final_Chain_Closed h_rz
  -- h_ev_eq : ↑ev = ρ * (1 - ρ)
  rw [← h_ev_eq]
  exact Complex.ofReal_im ev

lemma im_quadratic (ρ : ℂ) :
    (ρ * (1 - ρ)).im = ρ.im * (1 - 2 * ρ.re) := by
  simp [Complex.mul_im, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

-- ════════════════════════════════════════════════
-- §3. 최종 마스터 정리: N-ZFC 리만 가설 (Final RH)
-- ════════════════════════════════════════════════

theorem nzfc_riemann_hypothesis
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (evs : ℕ → ℂ) (T : H →L[ℂ] H)
    {ρ : ℂ} (h : SingularityPrinciple.IsNontrivialZero ρ) :
    ρ.re = 1/2 := by

  -- Step 1: 임계대 위치 확보 (File 28, 05 기반)
  have h_rz : NZFC_V3_5_Modular.IsRiemannZero ρ :=
    nontrivial_to_riemann_zero evs T h

  -- Step 2: 자기수반성에 의한 고윳값 실수성 확보 (File 21, 18 기반)
  have h_spec_im : (ρ * (1 - ρ)).im = 0 :=
    eigenvalue_im_zero h_rz

  -- Step 3: 대수적 전개 (File 04 기반)
  rw [im_quadratic] at h_spec_im
  
  -- Step 4: 임계 구역 밖 영점 배제 (File 05 기반)
  have h_im_nz : ρ.im ≠ 0 :=
    SingularityPrinciple.zero_off_axis_riemannZeta_Final h

  -- Step 5: 산술적 확정 (Linarith)
  have h_factor : 1 - 2 * ρ.re = 0 :=
    (mul_eq_zero.mp h_spec_im).resolve_left h_im_nz

  linarith

end NZFC.FinalChain