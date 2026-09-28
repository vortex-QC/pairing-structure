/-
# 投影假设特例化第四块: 四块谱族分解 (T_四1-T_四3, 2026-09-25)
对应: papers/对偶命题_投影假设特例化_第四块_四块谱族_v0.1.md
体系: 对偶命题 C4 严格化第四块——"完整谱分解重件"的离散内核

语义锚 (体系层·不进形式层):
  - 谱族三性质: 正交 (互斥) + 完备 (和=I) + 各自投影 (读数合法)——测量基=谱族的离散完整版
  - 四块 = 两约束的同时确认谱: {PQ, P(1−Q), (1−P)Q, (1−P)(1−Q)}
    = {双确认, 仅 P 确认, 仅 Q 确认, 双未确认}——两约束组合读数的完备分类
  - 对易=四块结构成立的前提 (Q 侧分界需对易——非对易时"仅 P 确认"块不在 Q 核内=互斥分界的谱面重述)
数学内容 (纯结构·点级——零 API 风险):
  T_四1 补的确认投影性: (1−M) 幂等+自伴 ("未确认"读数合法)
  T_四2 四块和=I (完备性·代数恒等)
  T_四3 代表对正交 (Q 侧+P 侧·乘积零统一路线——其余四对为同型引理换位实例·判读级登记)
边界 (如实标): 一般谱测度 (无限维连续谱) = 重件维持;
  本块=离散谱族 (双投影两点谱) 的完整形态。
-/
import Mathlib

open scoped InnerProductSpace

namespace DensityMath

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- 确认投影结构 (第一块同款·自包含重述)。 -/
structure ConfirmProj (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  M : E →L[ℂ] E
  idem : ∀ x, M (M x) = M x
  selfadj : ∀ x y, ⟪M x, y⟫_ℂ = ⟪x, M y⟫_ℂ

/-- 正交性 (第一块 T_C4.1 同款·自包含重述): x∈ker·y∈range ⟹ ⟪x,y⟫=0。 -/
theorem ortho_ker_range (P : ConfirmProj E) {x y : E} (hx : P.M x = 0) (hy : P.M y = y) :
    ⟪x, y⟫_ℂ = 0 := by
  rw [← hy, ← P.selfadj x y, hx, inner_zero_left]

/-! ## T_四1 补的确认投影性 -/

/-- **定理 T_四1a (补的幂等性)** (1−M) 幂等——"未确认"读数两次=一次。
体系语义: 未确认也是稳定读数 (确认谱 {0,1} 的 0 侧)。 -/
theorem comp_idem (P : ConfirmProj E) (x : E) :
    (x - P.M x) - P.M (x - P.M x) = x - P.M x := by
  have h : P.M (x - P.M x) = 0 := by
    rw [map_sub, P.idem, sub_self]
  rw [h, sub_zero]

/-- **定理 T_四1b (补的自伴性)** (1−M) 自伴——未确认读数取实。 -/
theorem comp_selfadj (P : ConfirmProj E) (x y : E) :
    ⟪x - P.M x, y⟫_ℂ = ⟪x, y - P.M y⟫_ℂ := by
  rw [inner_sub_left, inner_sub_right, P.selfadj x y]

/-! ## 核心正交引理 (P 侧分界 + Q 侧分界) -/

/-- **引理 T_四3a (P 侧分界)** P.M u ⊥ (v − P.M v)——range(P) 与 ker(P) 正交的对调形态。 -/
theorem ortho_P_side (P : ConfirmProj E) (u v : E) :
    ⟪P.M u, v - P.M v⟫_ℂ = 0 := by
  have h1 : ⟪v - P.M v, P.M u⟫_ℂ = 0 := by
    refine ortho_ker_range P ?_ (P.idem u)
    rw [map_sub, P.idem, sub_self]
  calc ⟪P.M u, v - P.M v⟫_ℂ = star ⟪v - P.M v, P.M u⟫_ℂ := (inner_conj_symm _ _).symm
    _ = star 0 := by rw [h1]
    _ = 0 := by simp

/-- **引理 T_四3b (Q 侧分界·需对易)** P.M (w − Q.M w) ⊥ Q.M z——
块 (sP)(1−Q) 的像在 ker Q 内 (对易: Q(P(w−Qw))=P(Q w−Q²w)=0)——
**非对易时此分界断裂=四块结构的前提**。 -/
theorem ortho_Q_side (P Q : ConfirmProj E)
    (hcomm : ∀ x, P.M (Q.M x) = Q.M (P.M x)) (w z : E) :
    ⟪P.M (w - Q.M w), Q.M z⟫_ℂ = 0 := by
  have hker : Q.M (P.M (w - Q.M w)) = 0 := by
    rw [← hcomm, map_sub, Q.idem, sub_self, map_zero]
  exact ortho_ker_range Q hker (Q.idem z)

/-! ## T_四2 四块和 = I (完备性) -/

/-- **定理 T_四2 (四块和=I)** 对任意态 x: PQx + P(1−Q)x + (1−P)Qx + (1−P)(1−Q)x = x——
两约束组合读数的完备分类 (谱族完备性·代数恒等)。 -/
theorem quad_decomp (P Q : ConfirmProj E) (x : E) :
    P.M (Q.M x) + P.M (x - Q.M x) + (P.M x - P.M (Q.M x))
      + (x - P.M x - (P.M x - P.M (Q.M x))) = x := by
  have hc : P.M (x - Q.M x) = P.M x - P.M (Q.M x) := map_sub _ _ _
  rw [hc]
  abel

/-! ## 乘积零统一路线 (对角外乘积=0 ⟹ 正交) -/

/-- 合成的自伴性 (第二块 T_谱1b 同款·自包含重述)。 -/
theorem compPair_selfadj (P Q : ConfirmProj E) (hcomm : ∀ x, P.M (Q.M x) = Q.M (P.M x)) (x y : E) :
    ⟪P.M (Q.M x), y⟫_ℂ = ⟪x, P.M (Q.M y)⟫_ℂ := by
  rw [P.selfadj (Q.M x) y, Q.selfadj x (P.M y), ← hcomm y]

/-- **引理 T_四3c (Q 侧乘积零)** P.M(Q.M(P.M(y−Q.M y))) = 0——
"仅 Q 确认"块复合在"仅 P 确认"块上=0 (Q 幂等+对易)。 -/
theorem prod_zero_Q (P Q : ConfirmProj E)
    (hcomm : ∀ x, P.M (Q.M x) = Q.M (P.M x)) (y : E) :
    P.M (Q.M (P.M (y - Q.M y))) = 0 := by
  rw [← hcomm, P.idem, map_sub, Q.idem, sub_self, map_zero]

/-- **引理 T_四3d (P 侧乘积零)** P.M(Q.M(Q.M y − P.M (Q.M y))) = 0——
"双确认"块复合在"仅 Q 确认"块上=0 (P 幂等+对易)。 -/
theorem prod_zero_P (P Q : ConfirmProj E)
    (hcomm : ∀ x, P.M (Q.M x) = Q.M (P.M x)) (y : E) :
    P.M (Q.M (Q.M y - P.M (Q.M y))) = 0 := by
  have hq : Q.M (Q.M y - P.M (Q.M y)) = Q.M y - P.M (Q.M y) := by
    rw [map_sub, Q.idem, ← hcomm (Q.M y), Q.idem]
  rw [hq, map_sub, P.idem, sub_self]

/-! ## T_四3 四块两两正交 (代表对·乘积零路线) -/

/-- **定理 T_四3-Q (互斥性代表对·Q 侧)** PQ x ⊥ P(1−Q) y——
"双确认"与"仅 P 确认"块正交 (乘积零: A(B y)=0 ⟹ ⟪A x, B y⟫=⟪x, A(B y)⟫=0)。 -/
theorem ortho_pair_Q (P Q : ConfirmProj E)
    (hcomm : ∀ x, P.M (Q.M x) = Q.M (P.M x)) (x y : E) :
    ⟪P.M (Q.M x), P.M (y - Q.M y)⟫_ℂ = 0 := by
  have hprod := prod_zero_Q P Q hcomm y
  calc ⟪P.M (Q.M x), P.M (y - Q.M y)⟫_ℂ
      = ⟪x, P.M (Q.M (P.M (y - Q.M y)))⟫_ℂ := compPair_selfadj P Q hcomm x (P.M (y - Q.M y))
    _ = ⟪x, 0⟫_ℂ := by rw [hprod]
    _ = 0 := by simp

/-- **定理 T_四3-P (互斥性代表对·P 侧)** PQ x ⊥ (Q y − P(Q y))——
"双确认"与"仅 Q 确认"块正交 (乘积零路线)。 -/
theorem ortho_pair_P (P Q : ConfirmProj E)
    (hcomm : ∀ x, P.M (Q.M x) = Q.M (P.M x)) (x y : E) :
    ⟪P.M (Q.M x), Q.M y - P.M (Q.M y)⟫_ℂ = 0 := by
  have hprod := prod_zero_P P Q hcomm y
  calc ⟪P.M (Q.M x), Q.M y - P.M (Q.M y)⟫_ℂ
      = ⟪x, P.M (Q.M (Q.M y - P.M (Q.M y)))⟫_ℂ := compPair_selfadj P Q hcomm x (Q.M y - P.M (Q.M y))
    _ = ⟪x, 0⟫_ℂ := by rw [hprod]
    _ = 0 := by simp

end DensityMath
