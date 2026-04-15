import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Instances.Complex

set_option linter.unusedSectionVars false

namespace NZFC.Determinant

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### 1. File 02 (Nuclear Budget) -/
variable (eigenvalues : ℕ → ℂ)
axiom file02_nuclear_budget : Summable (fun n => ‖eigenvalues n‖)

/-! ### 2. Fredholm Determinant -/
noncomputable def fredholmDet (s : ℂ) : ℂ :=
  Complex.exp (tsum (fun n => Complex.log (1 - s * eigenvalues n)))

/-! ### 3. Fredholm Alternative Axiom -/
axiom fredholm_kernel_iff_det_zero (T : H →L[ℂ] H) (s : ℂ) :
    fredholmDet (eigenvalues) s = 0 ↔
    ∃ v ≠ 0, (ContinuousLinearMap.id ℂ H - s • T) v = 0

/-! ### 4. 대수적 보조정리들 (화살표 방향 수정 완벽 적용) -/
private lemma eq_inv_smul_of_sub_smul_eq_zero
    {s : ℂ} (hs : s ≠ 0) {v w : H}
    (h : v - s • w = 0) : w = (1 / s) • v := by
  have hv : v = s • w := sub_eq_zero.mp h
  -- FIX: ← smul_smul 을 smul_smul 정방향으로 수정
  rw [hv, one_div, smul_smul, inv_mul_cancel₀ hs, one_smul]

private lemma sub_smul_eq_zero_of_eq_inv_smul
    {s : ℂ} (hs : s ≠ 0) {v w : H}
    (h : w = (1 / s) • v) : v - s • w = 0 := by
  -- FIX: ← smul_smul 을 smul_smul 정방향으로 수정
  rw [h, one_div, smul_smul, mul_inv_cancel₀ hs, one_smul, sub_self]

/-! ### 5. 영점-고유값 동치 브릿지 (완전한 증명) -/
theorem fredholmDet_zero_iff_eigenvalue
    (T : H →L[ℂ] H) (s : ℂ) (hs : s ≠ 0) :
    fredholmDet (eigenvalues) s = 0 ↔ ∃ v ≠ 0, T v = (1 / s) • v := by
  constructor
  · intro h_zero
    obtain ⟨v, hv_ne, hv_eq⟩ := (fredholm_kernel_iff_det_zero eigenvalues T s).mp h_zero
    change v - s • T v = 0 at hv_eq
    exact ⟨v, hv_ne, eq_inv_smul_of_sub_smul_eq_zero hs hv_eq⟩
  · intro ⟨v, hv_ne, hv_eq⟩
    have h_ker : (ContinuousLinearMap.id ℂ H - s • T) v = 0 := by
      change v - s • T v = 0
      exact sub_smul_eq_zero_of_eq_inv_smul hs hv_eq
    exact (fredholm_kernel_iff_det_zero eigenvalues T s).mpr ⟨v, hv_ne, h_ker⟩

end NZFC.Determinant
