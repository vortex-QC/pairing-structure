/-
# 投影假设特例化第三块: 完备性与有限维谱接口 (T_完1-T_完3+T_实谱+T_正交, 2026-09-25)
对应: papers/对偶命题_投影假设特例化_第三块_完备性与谱接口_v0.1.md
体系: 对偶命题 C4 严格化第三块 (第一块单投影/第二块投影族)

语义锚 (体系层·不进形式层):
  - 完备性件: 确认子空间=闭子空间 (确认态集合在极限下稳定——静的定型性的拓扑形态)
  - 正交特征性质: x−Mx ⊥ range(M) —— 确认投影=到闭子空间正交投影的特征刻画
    (Mathlib orthogonalProjection 接口的同名一致性=后续件·如实标)
  - 有限维谱接口: 自伴算子谱实 (读数取实=D2) + 异谱正交 (互斥且完备——β 来源档 P3 正交结构的谱版)
数学内容 (纯结构):
  T_完1: range(M) = ker(M − I) (确认子空间的核形态)
  T_完2: range(M) 闭 (isClosed_ker——完备空间语境)
  T_完3: x − M x ⊥ range(M) (正交特征性质·全范围版)
  T_实谱: 自伴算子特征值实 (conj a = a)
  T_正交: 自伴算子异谱特征向量正交
-/
import Mathlib

open scoped InnerProductSpace

namespace DensityMath

/-- 确认投影结构 (第一块同款·ℂ 域)。 -/
structure ConfirmProj (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  M : E →L[ℂ] E
  idem : ∀ x, M (M x) = M x
  selfadj : ∀ x y, ⟪M x, y⟫_ℂ = ⟪x, M y⟫_ℂ

/-! ## 完备性件 (希尔伯特空间语境) -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- **定理 T_完1 (确认子空间的核形态)** range(M) = ker(M − I)——
确认子空间=复合算子 (M−I) 的核 (纯代数·两方向)。 -/
theorem range_eq_ker_sub_id (P : ConfirmProj E) (x : E) :
    (∃ y, P.M y = x) ↔ (P.M - ContinuousLinearMap.id ℂ E) x = 0 := by
  constructor
  · rintro ⟨y, hy⟩
    -- x = M y ⟹ (M−I) x = M(M y) − M y = 0 (幂等)
    have : P.M x = x := by rw [← hy, P.idem]
    simpa using sub_eq_zero.mpr (by rw [this])
  · intro h
    refine ⟨x, ?_⟩
    have h2 : P.M x - x = 0 := by simpa using h
    exact sub_eq_zero.mp h2

omit [CompleteSpace E] in
/-- **定理 T_完2 (确认子空间闭)** range(M) 闭——
确认态集合在极限下稳定 (静的定型性的拓扑形态·isClosed_ker——核的闭性不需要完备性)。 -/
theorem range_closed (P : ConfirmProj E) :
    IsClosed {x : E | ∃ y, P.M y = x} := by
  have hker : IsClosed ((P.M - ContinuousLinearMap.id ℂ E).ker : Set E) :=
    ContinuousLinearMap.isClosed_ker _
  have hset : {x : E | ∃ y, P.M y = x} = ((P.M - ContinuousLinearMap.id ℂ E).ker : Set E) := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      have hmx : P.M x = x := by rw [← hy, P.idem]
      simpa using sub_eq_zero.mpr hmx
    · intro h
      have h2 : P.M x - x = 0 := by simpa using h
      exact ⟨x, sub_eq_zero.mp h2⟩
  rw [hset]
  exact hker

omit [CompleteSpace E] in
/-- **定理 T_完3 (正交特征性质)** x − M x ⊥ range(M) (全范围版)——
确认投影=到闭子空间正交投影的特征刻画 (y∈range ⟹ ⟪x−Mx, y⟫=0)。
Mathlib orthogonalProjection 接口的同名一致性=后续件·如实标。 -/
theorem orthogonal_character (P : ConfirmProj E) (x y : E) (hy : P.M y = y) :
    ⟪x - P.M x, y⟫_ℂ = 0 := by
  have h1 : ⟪x - P.M x, y⟫_ℂ = ⟪x, y⟫_ℂ - ⟪P.M x, y⟫_ℂ := inner_sub_left x (P.M x) y
  rw [h1, P.selfadj x y, hy, sub_self]

/-! ## 有限维谱接口 (自伴算子·ℂ) -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **定理 T_实谱 (特征值实)** 自伴算子的特征值实 (conj a = a)——
读数取实 (D2 比值可观测的谱形态: 确认读数落在实轴)。 -/
theorem eigenvalue_real {A : F →L[ℂ] F} (hA : ∀ x y, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    {x : F} (hx : x ≠ 0) {a : ℂ} (h : A x = a • x) : star a = a := by
  have h1 : ⟪A x, x⟫_ℂ = ⟪x, A x⟫_ℂ := hA x x
  rw [h, inner_smul_left, inner_smul_right] at h1
  have h5 : star a * ⟪x, x⟫_ℂ = a * ⟪x, x⟫_ℂ := h1
  have h3 : ⟪x, x⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hx
  exact mul_left_injective₀ h3 h5

/-- **定理 T_正交 (异谱正交)** 自伴算子不同特征值的特征向量正交——
确认谱的互斥且完备结构 (β 来源档 P3 正交结构的谱版)。 -/
theorem eigenvector_orthogonal {A : F →L[ℂ] F} (hA : ∀ x y, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    {x y : F} (hx : x ≠ 0) {a b : ℂ} (hxa : A x = a • x) (hyb : A y = b • y) (hab : a ≠ b) :
    ⟪x, y⟫_ℂ = 0 := by
  have hca' : (starRingEnd ℂ) a = a := eigenvalue_real hA hx hxa
  have h1 : ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ := hA x y
  rw [hxa, inner_smul_left, hyb, inner_smul_right] at h1
  rw [hca'] at h1
  have hz : (a - b) * ⟪x, y⟫_ℂ = 0 := by
    rw [sub_mul, ← h1, sub_self]
  rcases mul_eq_zero.mp hz with h0 | h2
  · exact absurd h0 (sub_ne_zero.mpr hab)
  · exact h2

end DensityMath
