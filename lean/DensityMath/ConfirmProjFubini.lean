/-
# 投影假设特例化第七块: 一般 n 格点和归一 (Fubini 件) (T_F1-T_F3, 2026-09-26)
对应: papers/对偶命题_投影假设特例化_第七块_Fubini归一_v0.1.md
体系: 对偶命题线·投影假设形式级续块 —— 第六块挂账"格点和=I 归一 (Fubini 件)"清偿

API 盘点更正 (去幻登记): 第六块记 "prod_univ_sum 零命中 (无承重件)" —— 本块复核发现
  Finset.prod_univ_sum 在 Mathlib/Algebra/BigOperators/Ring/Finset.lean:157 在版
  (∏ i, ∑ j ∈ t i, f i j = ∑ x ∈ piFinset t, ∏ i, f i (x i)) —— 零命中系检索面不全,
  非上游缺失; "候 Mathlib 上游或自建 measure 层"降为"承重在版+推论两步".

数学内容 (纯结构·NNReal 上·无需测度论/拓扑/完备性):
  T_F1 一般 n 格点和归一 (主件): ∑_v ∏_i f_i(v_i) = ∏_i (f_i(false)+f_i(true))
  T_F2 联合谱测度归一: 每约束二值归一 ⟹ 全格点和 = 1 (第六块 §一.3 缺口直接清偿)
  T_F3 互补归一: 任意格点子集 s 的读数与补集读数之和 = 1 (μ(s)+μ(sᶜ)=1 的一般 n 形态)
语义锚 (体系层·不进形式层): m_i(true)=主侧读数 (side M_i 形态), m_i(false)=补侧;
  格点 v = 约束族的原子 (2ⁿ 格·第六块 jointAtomN); μ(s)=∑ 原子 = 谱测度读出.
边界 (如实标): 连续谱/无限维谱测度不在本块 (维持挂账·真 measure 层).
-/
import Mathlib

namespace ConfirmProjFubini

/-- Bool 全域求和展开 (Bool.univ = {false, true}) —— 辅助引理. -/
theorem sum_univ_bool' {M : Type*} [AddCommMonoid M] (g : Bool → M) :
    ∑ j ∈ (Finset.univ : Finset Bool), g j = g false + g true := by
  have huniv : (Finset.univ : Finset Bool) = {false, true} := by
    ext j; simp
  rw [huniv]; simp

/-- T_F1 一般 n 格点和归一 (主件): 逐约束两支和的积 = 全格点原子和.
    承重: Finset.prod_univ_sum (Mathlib 在版·见头注 API 更正). -/
theorem grid_sum_norm {n : ℕ} (f : Fin n → Bool → NNReal) :
    ∑ v : Fin n → Bool, ∏ i, f i (v i) = ∏ i, (f i false + f i true) := by
  have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Bool)) f
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  exact Finset.prod_congr rfl (fun i _ => sum_univ_bool' (f i))

/-- T_F2 联合谱测度归一 (一般 n): 每约束二值归一 ⟹ 全格点原子和 = 1.
    第六块挂账"格点和=I 归一"直接清偿 (语义: ∑_v μ(v) = I). -/
theorem joint_measure_univ {n : ℕ} (m : Fin n → Bool → NNReal)
    (hnorm : ∀ i, m i false + m i true = 1) :
    ∑ v : Fin n → Bool, ∏ i, m i (v i) = 1 := by
  rw [grid_sum_norm m]
  simp [hnorm]

/-- T_F3 互补归一 (一般 n): 任意格点子集 s 的读数与补集读数之和 = 1
    (μ(s) + μ(sᶜ) = 1 的格点测度形态·承重 union_compl + sum_union). -/
theorem measure_compl {n : ℕ} (m : Fin n → Bool → NNReal)
    (hnorm : ∀ i, m i false + m i true = 1) (s : Finset (Fin n → Bool)) :
    (∑ v ∈ s, ∏ i, m i (v i)) + (∑ v ∈ sᶜ, ∏ i, m i (v i)) = 1 := by
  have h := joint_measure_univ m hnorm
  rw [← Finset.union_compl s, Finset.sum_union (disjoint_compl_right (a := s))] at h
  exact h

#print axioms ConfirmProjFubini.sum_univ_bool'
#print axioms ConfirmProjFubini.grid_sum_norm
#print axioms ConfirmProjFubini.joint_measure_univ
#print axioms ConfirmProjFubini.measure_compl

end ConfirmProjFubini
