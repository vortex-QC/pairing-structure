/-
# 投影假设特例化第二块: 谱定理接口——投影族与对易结构 (T_谱1-T_谱3, 2026-09-25)
对应: papers/对偶命题_投影假设特例化_第二块_谱定理接口_v0.1.md
体系: 对偶命题 C4 严格化第二块 (第一块 ConfirmProj.lean: 三条约束=>正交投影)

语义锚 (体系层·不进形式层):
  - 测量基←约束族 (C4 档要素对应): 谱族=确认投影族 {M_i}·每个 M_i=一条约束的确认动作
  - 对易=比值可并存 (定理 4.4 对易面): 两约束的对易确认投影——复合不动点=两约束各自确认——同时确认
  - 非对易=单值确认互斥 (定理 4.4 非对易面): 不对易投影不可同时确认
    (体系语义: 共轭量的确认投影不对易——互斥结构读法·元约束 ħ=量化记号)
数学内容 (纯结构·内积空间层面):
  T_谱1 对易合成幂等: 对易的两确认投影之合成幂等 (复合显化定型)
  T_谱1b 合成自伴: 复合读数仍取实值
  T_谱2 公共确认: 复合不动点 ⟹ 两投影各自不动点 (⊆) / 两投影不动点 ⟹ 复合不动点 (⊇)
  T_谱3 非对易反例: 显式 2×2 实矩阵——各自幂等对称·但 PQ≠QP (单值确认互斥实例)
边界 (如实标): 完整谱分解定理 (自伴算子谱族) = 后续重件; Born 权重边界维持。
-/
import Mathlib

open scoped InnerProductSpace

namespace DensityMath

/-- 确认投影结构 (第一块 ConfirmProj 同款·自包含重述)。 -/
structure ConfirmProj (𝕜 : Type*) [RCLike 𝕜] (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] where
  M : E →L[𝕜] E
  idem : ∀ x, M (M x) = M x
  selfadj : ∀ x y, ⟪M x, y⟫_𝕜 = ⟪x, M y⟫_𝕜

/-! ## T_谱1 对易合成 -/

/-- **定理 T_谱1a (合成的幂等性)** 对易的两确认投影之合成幂等——
同时确认两次=同时确认一次 (复合显化定型)。 -/
theorem comp_idem {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (P Q : ConfirmProj 𝕜 E)
    (hcomm : ∀ x, P.M (Q.M x) = Q.M (P.M x)) (x : E) :
    P.M (Q.M (P.M (Q.M x))) = P.M (Q.M x) := by
  have h1 : P.M (Q.M (P.M (Q.M x))) = P.M (Q.M (Q.M (P.M x))) := by
    congr 2
    exact hcomm x
  rw [h1, Q.idem, ← hcomm, P.idem]

/-- **定理 T_谱1b (合成的自伴性)** 对易的两确认投影之合成自伴——
复合读数仍取实值 (同时确认的读数性·D2 算子形态在复合下保持)。 -/
theorem comp_selfadj {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (P Q : ConfirmProj 𝕜 E)
    (hcomm : ∀ x, P.M (Q.M x) = Q.M (P.M x)) (x y : E) :
    ⟪P.M (Q.M x), y⟫_𝕜 = ⟪x, P.M (Q.M y)⟫_𝕜 := by
  rw [P.selfadj (Q.M x) y, Q.selfadj x (P.M y), ← hcomm y]

/-! ## T_谱2 公共确认 (同时确认=两投影各自确认) -/

/-- **定理 T_谱2a (复合不动点 ⟹ 各自确认)** P.M (Q.M x) = x ⟹ P.M x = x——
被复合读数确认的态被第一个约束确认 (同时确认的第一半)。 -/
theorem comp_fixed_M {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (P Q : ConfirmProj 𝕜 E) {x : E} (h : P.M (Q.M x) = x) :
    P.M x = x := by
  rw [← h, P.idem]

/-- **定理 T_谱2b (复合不动点 ⟹ 各自确认·第二支)** P.M (Q.M x) = x ⟹ Q.M x = x——
第二支需要对易 (Q.M x = Q.M(P.M(Q.M x)) = P.M(Q.M(Q.M x)) = P.M(Q.M x) = x)。
体系语义: 同时确认的态被两约束**分别**确认——对易=比值可并存 (定理 4.4 对易面)。 -/
theorem comp_fixed_N {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (P Q : ConfirmProj 𝕜 E)
    (hcomm : ∀ x, P.M (Q.M x) = Q.M (P.M x)) {x : E} (h : P.M (Q.M x) = x) :
    Q.M x = x := by
  have h2 : Q.M x = Q.M (P.M (Q.M x)) := by rw [h]
  rw [h2, hcomm, Q.idem, ← hcomm, h]

/-- **定理 T_谱2c (各自确认 ⟹ 复合确认)** 两投影各自不动点 ⟹ 复合不动点——
交集⊆复合像 (同时确认的逆方向·无需对易)。 -/
theorem comp_range_sup {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (P Q : ConfirmProj 𝕜 E) {x : E}
    (hxM : P.M x = x) (hxN : Q.M x = x) : P.M (Q.M x) = x := by
  rw [hxN, hxM]

/-! ## T_谱3 非对易反例 (单值确认互斥的算子实例) -/

/-- **P 的幂等性**——P=[[1,0],[0,0]]（投影到 e₁·对称幂等=确认投影的 ℝ 矩阵形态）。 -/
theorem proj_P_idem :
    Matrix.of ![![1, 0], ![0, 0]] * Matrix.of ![![1, 0], ![0, 0]] = Matrix.of ![![1, 0], ![0, 0]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.of_apply]

/-- Q 的幂等性 (rank-1 投影)。 -/
theorem proj_Q_idem :
    Matrix.of ![![1/2, 1/2], ![1/2, 1/2]] * Matrix.of ![![1/2, 1/2], ![1/2, 1/2]]
      = Matrix.of ![![1/2, 1/2], ![1/2, 1/2]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.of_apply]

/-- **定理 T_谱3 (非对易核心等式)** PQ 的 (0,1) 元 = 1/2 而 QP 的 (0,1) 元 = 0——
**PQ ≠ QP**——两约束各自的确认动作合法·却不可交换 (确认顺序不同结果不同=
同时确认不存在公共形态——定理 4.4 非对易面=单值确认互斥的算子实例)。 -/
theorem noncommuting_core :
    (((Matrix.of ![![1, 0], ![0, 0]] * Matrix.of ![![1/2, 1/2], ![1/2, 1/2]]) :
        Matrix (Fin 2) (Fin 2) ℝ) 0 1) = (1/2 : ℝ) ∧
    (((Matrix.of ![![1/2, 1/2], ![1/2, 1/2]] * Matrix.of ![![1, 0], ![0, 0]]) :
        Matrix (Fin 2) (Fin 2) ℝ) 0 1) = (0 : ℝ) := by
  constructor <;> norm_num [Matrix.mul_apply, Matrix.of_apply]

end DensityMath
