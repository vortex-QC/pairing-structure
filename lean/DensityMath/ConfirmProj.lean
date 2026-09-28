/-
# 投影假设特例化第一块: 三条约束 => 正交投影 (T_C4.1-T_C4.3, 2026-09-25)
对应: papers/对偶命题_投影假设特例化_第一块_v0.1.md (对偶命题线挂账 2 执行件·C4 严格化)
体系: 对偶命题 C4 特例化王冠的结构级 → 形式级第一块 (构造数学线)

语义锚 (体系层·不进形式层——数学形态层/体系语义层分离见总标准 §五):
  - 确认动作 M: 幂等自映射 (显化算子·静的显化定义 4.1 在案·读出吞动=定理 4.5 语义)
  - 域约束+形式约束: 态空间=内积空间·M 线性有界 (★线性=形式约束新增内容·如实标:
    体系内显化算子不预设线性——本步是特例化的形式约束内容, 非体系内推出)
  - 自伴=实值读数性 (D2 比值可观测的算子形态: 读数取实 ⟺ 谱实 ⟺ 自伴)
数学内容 (纯结构·内积空间层面·不需要完备性——假设更少):
  T_C4.1 正交性: ker(M) ⊥ range(M) —— 确认子空间与被丢弃子空间读数互斥
  T_C4.2 塌缩分解: x = Mx + (x−Mx)·ker∩range=0 —— 塌缩=丢 ker 留 range 的数学形态
  T_C4.3 读数谱: 特征值 ∈ {0,1} —— 确认读数的"是/否"形态
边界 (如实标): Born 权重 (塌缩的统计规则) 不在三条约束内——实现条件·无来源。
-/
import Mathlib

open scoped InnerProductSpace

namespace DensityMath

/-- 确认投影结构: M 线性有界 (域约束的算子形态) + 幂等 (显化·静的显化定义 4.1)
+ 自伴 (实值读数性·D2 比值可观测的算子形态)。 -/
structure ConfirmProj (𝕜 : Type*) [RCLike 𝕜] (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] where
  M : E →L[𝕜] E
  idem : ∀ x, M (M x) = M x
  selfadj : ∀ x y, ⟪M x, y⟫_𝕜 = ⟪x, M y⟫_𝕜

/-! ## T_C4.1 正交性 -/

/-- **定理 T_C4.1 (正交性)** x∈ker(M)·y∈range(M) ⟹ ⟪x,y⟫=0——
确认子空间与被丢弃子空间正交。
体系语义: 读出吞动=投影丢掉 ker 分量·两分量读数互斥（定理 4.4 单值必有损的算子形态）。 -/
theorem range_orthogonal_ker {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (P : ConfirmProj 𝕜 E) {x y : E}
    (hx : P.M x = 0) (hy : P.M y = y) : ⟪x, y⟫_𝕜 = 0 := by
  rw [← hy, ← P.selfadj x y, hx, inner_zero_left]

/-! ## T_C4.2 塌缩分解 -/

/-- **定理 T_C4.2a (分解存在)** 任意态 x = M x + (x − M x)——确认分量+被丢弃分量。
体系语义: 塌缩的数学形态=确认动作丢掉 ker 分量留 range 分量。 -/
theorem collapse_decomp {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (P : ConfirmProj 𝕜 E) (x : E) :
    x = P.M x + (x - P.M x) := by
  abel

/-- **定理 T_C4.2b (分解唯一·交集零)** ker ∩ range = {0}——
分解唯一（塌缩结果确定·非随机——Born 权重的随机性不在本结构内·如实标）。 -/
theorem ker_inter_range {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (P : ConfirmProj 𝕜 E) {z : E}
    (h1 : P.M z = 0) (h2 : P.M z = z) : z = 0 := by
  have h3 : ⟪z, z⟫_𝕜 = 0 := range_orthogonal_ker P h1 h2
  exact inner_self_eq_zero.mp h3

/-- 被丢弃分量确实在 ker 中: M (x − M x) = 0 (幂等性直接推论)。 -/
theorem discard_in_ker {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (P : ConfirmProj 𝕜 E) (x : E) : P.M (x - P.M x) = 0 := by
  rw [map_sub, P.idem, sub_self]

/-- **定理 T_C4.2c (塌缩后重读不变)** 确认分量 M x 再确认不变 (幂等·读出定型)。
体系语义: 显化幂等性的算子形态——读出一次后再读不改变任何东西 (静是定型的)。 -/
theorem collapse_stable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (P : ConfirmProj 𝕜 E) (x : E) : P.M (P.M x) = P.M x := P.idem x

/-! ## T_C4.3 读数谱 -/

/-- **定理 T_C4.3 (确认读数谱)** 幂等算子的特征值 ∈ {0,1}——
确认读数的"是/否"形态（本征值=确认成功/未确认——测量基的投影读数）。
边界: 特征值的**概率分布** (Born 权重) 不在本结构内——实现条件·无来源·如实标。 -/
theorem eigenvalue_mem {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (P : ConfirmProj 𝕜 E) {x : E} (hx : x ≠ 0) {a : 𝕜}
    (h : P.M x = a • x) : a = 0 ∨ a = 1 := by
  have h2 : P.M (P.M x) = P.M x := P.idem x
  rw [h, map_smul, h, smul_smul] at h2
  have h3 : (a * a - a) • x = 0 := by
    rw [sub_smul, h2, sub_self]
  have h4 : a * a - a = 0 := by
    by_contra hne
    exact hx ((smul_eq_zero.mp h3).resolve_left hne)
  have h5 : a * (a - 1) = 0 := by
    have h6 : a * (a - 1) = a * a - a := by ring
    rw [h6, h4]
  rcases mul_eq_zero.mp h5 with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

end DensityMath
