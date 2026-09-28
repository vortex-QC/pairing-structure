/-
# 观察点网络: 维数语义面 (线性承重层, 2026-09-26 晚轻件)
对应: papers/观察点钉扎层级_ObservationNet推广_v0.1.md 候令清单 "维数语义面" (中偏大件)
体系: 层级表 "1 点全动 → 2 点钉线 → 3 点钉面 → 4 点钉架" 的维数语义 kernel 化 ——
  序结构面 (DualityNet) 之外的另一可形式化面: 每级冻结几维 = 仿射张成维数.
  线性承重四件:
    T_D1 两点线形读出唯一 (2 点钉线) /
    T_D2 平面饱和: ℝ² 中 4 点必仿射相关 = T_N7 "第 4 观察点无新级" 的维数版 /
    T_D3 三点钉面读数唯一 (重心读数唯一=平面被钉住·3 点钉面) /
    T_D4 手性核: 定向泛函 det2 (swap 反对称/退化自检/非退化⟹对独立).
边界 (如实标): 实例化在 ℝ² (EuclideanSpace·自反 AddTorsor) —— 一般流形/更高维不入本块;
  "三点仿射独立 ⟺ det2≠0" 的双向刻画只做线性读数唯一方向 (仿射 API 迁移=挂账);
  翻译层纪律: 定理级=抽象结构内.
-/
import Mathlib

namespace ObservationDims

/-- 平面内二维点 (EuclideanSpace ℝ (Fin 2)·自反 AddTorsor). -/
abbrev P2 := EuclideanSpace ℝ (Fin 2)

/-- 有向面积 (叉积标量): 手性/定向的承重量. -/
noncomputable def det2 (u v : P2) : ℝ := u 0 * v 1 - u 1 * v 0

/-! ### det2 线性族 (定向泛函的代数性质) -/

theorem det2_add_left (u w v : P2) : det2 (u + w) v = det2 u v + det2 w v := by
  simp only [det2, WithLp.ofLp_add, Pi.add_apply, mul_add, mul_sub]
  ring

theorem det2_add_right (u v w : P2) : det2 u (v + w) = det2 u v + det2 u w := by
  simp only [det2, WithLp.ofLp_add, Pi.add_apply, mul_add, sub_add_eq_add_sub]
  ring

theorem det2_smul_left (r : ℝ) (u v : P2) : det2 (r • u) v = r * det2 u v := by
  simp only [det2, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem det2_smul_right (r : ℝ) (u v : P2) : det2 u (r • v) = r * det2 u v := by
  simp only [det2, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem det2_zero_left (v : P2) : det2 0 v = 0 := by
  simp [det2, WithLp.ofLp_zero]

theorem det2_zero_right (u : P2) : det2 u 0 = 0 := by
  simp [det2, WithLp.ofLp_zero]

/-- T_D4a 手性核: 定向泛函 swap 反对称 —— 交换两点手性翻转 (3 点行手性的代数核). -/
theorem det2_swap (u v : P2) : det2 v u = -det2 u v := by
  simp only [det2]
  ring

/-- T_D4b 手性核: 退化自检 —— 同向量定向为零. -/
theorem det2_self (u : P2) : det2 u u = 0 := by
  simp only [det2]
  ring

/-! ### 线性独立与定向 -/

/-- T_D4c 手性核: 定向非退化 ⟹ 两向量对独立 ——
    非零有向面积把一对向量钉住 (手性=确认通道的最小非退化形态). -/
theorem linInd_of_det2_ne_zero {u v : P2} (hd : det2 u v ≠ 0) :
    LinearIndependent ℝ ![u, v] := by
  have hs_of : ∀ s t : ℝ, s • u + t • v = 0 → s = 0 := by
    intro s t hst
    have e1 : s * det2 u v + t * det2 v v = det2 (s • u + t • v) v := by
      rw [det2_add_left, det2_smul_left, det2_smul_left]
    have e2 : det2 (s • u + t • v) v = det2 (0 : P2) v := by rw [hst]
    rw [det2_self, mul_zero, add_zero, e2, det2_zero_left] at e1
    rcases mul_eq_zero.mp e1 with h | h
    · exact h
    · exact absurd h hd
  rw [LinearIndependent.pair_iff]
  intro s t hst
  refine ⟨hs_of s t hst, ?_⟩
  rw [hs_of s t hst, zero_smul, zero_add] at hst
  rcases smul_eq_zero.mp hst with h2 | h2
  · exact h2
  · exfalso
    rw [h2] at hd
    exact absurd (det2_zero_right u) hd

/-! ### 维数语义面四件 -/

/-- T_D1 两点线形读出唯一: 两个不同点的仿射组合 (权重和 1) 表示唯一 ——
    层级表 "2 点钉线" 的线性承重 (连线被两点钉住·线上读数=单参数). -/
theorem line_readout_unique {p q : P2} (hpq : p ≠ q) {a b a' b' : ℝ}
    (ha : a + b = 1) (ha' : a' + b' = 1)
    (h : a • p + b • q = a' • p + b' • q) : a = a' ∧ b = b' := by
  have hco : (a - a') • p + (b - b') • q = (0 : P2) := by
    linear_combination (norm := module) h
  have hbb : b - b' = -(a - a') := by linarith
  rw [hbb, neg_smul] at hco
  have hkey : (a - a') • (p - q) = (0 : P2) := by
    rw [smul_sub]
    exact hco
  rcases smul_eq_zero.mp hkey with h1 | h1
  · exact ⟨by linarith [h1], by linarith [h1, hbb]⟩
  · exact absurd (sub_eq_zero.mp h1) hpq

/-- T_D2 平面饱和 (T_N7 维数版): ℝ² 中 4 点必仿射相关 ——
    "3 点钉面后第 4 观察点不升维" 的线性承重 (仿射独立族基数 ≤ dim+1 = 3). -/
theorem four_points_affine_dependent {p₁ p₂ p₃ p₄ : P2} :
    ¬ AffineIndependent ℝ (![p₁, p₂, p₃, p₄] : Fin 4 → P2) := by
  intro h
  have h1 := h.card_le_finrank_succ
  rw [Fintype.card_fin] at h1
  have h2 : Module.finrank ℝ
      (vectorSpan ℝ (Set.range (![p₁, p₂, p₃, p₄] : Fin 4 → P2))) ≤ 2 :=
    le_trans (Submodule.finrank_le _) (le_of_eq finrank_euclideanSpace_fin)
  linarith

/-- T_D3 三点钉面读数唯一: 定向非退化 ⟹ 三点的重心组合 (权重和 1) 表示唯一 ——
    层级表 "3 点钉面" 的线性承重 (平面被三点钉住·面上读数=双参数).
    语义: 重心坐标唯一 = 面内每点有唯一 "钉扎读数" (对齐 T_对2 塌缩点读出相容). -/
theorem plane_readout_unique (p₀ p₁ p₂ : P2) (hd : det2 (p₁ - p₀) (p₂ - p₀) ≠ 0)
    {w w' : Fin 3 → ℝ} (hw : w 0 + w 1 + w 2 = 1) (hw' : w' 0 + w' 1 + w' 2 = 1)
    (hx : w 0 • p₀ + w 1 • p₁ + w 2 • p₂
        = w' 0 • p₀ + w' 1 • p₁ + w' 2 • p₂) :
    w 0 = w' 0 ∧ w 1 = w' 1 ∧ w 2 = w' 2 := by
  have hco : (w 0 - w' 0) • p₀ + (w 1 - w' 1) • p₁ + (w 2 - w' 2) • p₂ = (0 : P2) := by
    linear_combination (norm := module) hx
  have hw0 : w 0 - w' 0 = -(w 1 - w' 1) - (w 2 - w' 2) := by linarith
  rw [hw0] at hco
  have key : (w 1 - w' 1) • (p₁ - p₀) + (w 2 - w' 2) • (p₂ - p₀) = (0 : P2) := by
    linear_combination (norm := module) hco
  have hpair := (linInd_of_det2_ne_zero hd).eq_zero_of_pair key
  exact ⟨by linarith [hw0, hpair.1, hpair.2], by linarith [hpair.1], by linarith [hpair.2]⟩

#print axioms ObservationDims.det2_swap
#print axioms ObservationDims.det2_self
#print axioms ObservationDims.linInd_of_det2_ne_zero
#print axioms ObservationDims.line_readout_unique
#print axioms ObservationDims.four_points_affine_dependent
#print axioms ObservationDims.plane_readout_unique

end ObservationDims
