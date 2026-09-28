/-
# 投影假设特例化第五块: 一般谱测度 (离散原子版) + 对易两面定理 (2026-09-25)
对应: papers/对偶命题_投影假设特例化_第五块_一般谱测度_v0.1.md
体系: 对偶命题 C4 严格化第五块——日总 §30 下会话入口①「一般谱测度重件」

★API 盘点结论 (2026-09-25·E1 留痕·Mathlib v4.33.1 全库 grep·先于写码):
  - "spectralFamily|spectralMeasure" 零命中 / "HasSpectralFamily" 零命中 / "GeneralizedEigenvector" 零命中
    ⇒ 谱族/谱测度/广义本征向量无 Mathlib 承重件——连续谱无限维谱测度本版不可直接落地
  - 承重面改走: Analysis/InnerProductSpace/JointEigenspace.lean (对易族同时本征分解·有限维)
    + Analysis/InnerProductSpace/Spectrum.lean (自伴谱件) + 自建二值侧代数
本块两组:
  一、对易两面 (入口②):
    T_谱G1a 必要性·有限维: 公共特征正交基 ⟹ 对易
    T_谱G1b 必要性·无限维: 公共特征向量族张成稠密 ⟹ 对易 (不要求完备基)
    T_谱G2a/G2b 逆否: 非对易 ⟹ 无公共特征正交基 / 公共特征族不稠密
    T_谱G3/G3b 存在面·Mathlib 承重登记: 对易对称对/族 (有限维) ⟹ 联合本征分解=⊤
    ⇒ 两面合流 (判读级): 有限维「可同时确认 ⟺ 对易」——C4 要素对应表"测量基←约束族"双面闭合
  二、离散原子谱测度 (入口③的在版最大形态):
    二值侧算子族 side M : Fin 2 → CLM (确认侧 M / 未确认侧 1−M)——幂等+互斥+归一
    联合格点原子 jointAtom (a,b) = side P.M a * side Q.M b (对易假设下):
    T_谱μ0 原子幂等 / T_谱μ0b 原子互斥 (全对——第四块两个代表对升格) /
    T_谱μ2 归一 / T_谱μ3 任意子集读出合法 (μ(s)²=μ(s)) / T_谱μ4 有限可加
边界 (如实标): 连续谱/无限维谱测度挂账 (Mathlib 无承重件); Born 权重无来源 (同前四块);
  存在面的"联合分解→公共特征 ONB 组装"=工程级登记不展开。
-/
import Mathlib

open scoped InnerProductSpace
open scoped Function

namespace DensityMath

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- 确认投影结构 (前四块同款·自包含重述)。 -/
structure ConfirmProj (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  M : E →L[ℂ] E
  idem : ∀ x, M (M x) = M x
  selfadj : ∀ x y, ⟪M x, y⟫_ℂ = ⟪x, M y⟫_ℂ

/-! ## 二值侧算子族 (单算子谱代数) -/

/-- **二值侧算子族**: side M 1 = M (确认侧) / side M 0 = 1 − M (未确认侧)——
单算子读数谱 {0,1} 的算子化, 谱测度的原子层。 -/
def side (M : E →L[ℂ] E) : Fin 2 → (E →L[ℂ] E) := fun a => if a = 1 then M else 1 - M

/-- **T_谱A1 (侧幂等)** side M a 复合自身 = 自身——确认/未确认读数各自稳定。 -/
theorem side_self_mul (M : E →L[ℂ] E) (hidem : ∀ x, M (M x) = M x) (a : Fin 2) :
    side M a * side M a = side M a := by
  refine ContinuousLinearMap.ext fun x => ?_
  fin_cases a <;> simp_all [side]

/-- **T_谱A2 (侧互斥)** a ≠ a' ⟹ side M a * side M a' = 0——
确认侧与未确认侧互相吞没 (读出吞动的复合形态)。 -/
theorem side_mul_zero (M : E →L[ℂ] E) (hidem : ∀ x, M (M x) = M x) (a a' : Fin 2) (h : a ≠ a') :
    side M a * side M a' = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  fin_cases a <;> fin_cases a' <;> simp_all [side]

/-- **T_谱A3 (侧归一)** side M 0 + side M 1 = 1——读数谱完备 (确认+未确认=全体)。 -/
theorem side_sum (M : E →L[ℂ] E) : ∑ a : Fin 2, side M a = 1 := by
  rw [Fin.sum_univ_two]
  refine ContinuousLinearMap.ext fun x => ?_
  simp [side]
  all_goals exact sub_add_cancel x (M x)

/-- **T_谱A4 (交叉对易)** P 侧与 Q 侧任意格点复合可交换 (对易假设的四象限封闭)——
第四块"对易=四块结构前提"的格点化全展开。 -/
theorem side_commute (P Q : ConfirmProj E) (hcomm : ∀ x, P.M (Q.M x) = Q.M (P.M x))
    (a b : Fin 2) : side P.M a * side Q.M b = side Q.M b * side P.M a := by
  refine ContinuousLinearMap.ext fun x => ?_
  fin_cases a <;> fin_cases b <;> simp_all [side]
  all_goals (try abel)

/-! ## 联合格点原子与谱测度 (两约束 2×2) -/

/-- **联合谱原子**: 格点 (a,b) 的读出算子 = P 侧 × Q 侧——
第四块四块谱族 {PQ, P(1−Q), (1−P)Q, (1−P)(1−Q)} 的格点化重述。 -/
def jointAtom (P Q : ConfirmProj E) (a b : Fin 2) : E →L[ℂ] E := side P.M a * side Q.M b

/-- 联合格点测度: 任意格点子集 ↦ 原子之和。 -/
def jointMeasure (P Q : ConfirmProj E) (s : Finset (Fin 2 × Fin 2)) : E →L[ℂ] E :=
  ∑ p ∈ s, jointAtom P Q p.1 p.2

/-- **核心重排引理**: 两原子复合 = (P 侧各自复合) × (Q 侧各自复合)——
交叉对易承担全部重排 (第四块"乘法结构显形"的格点化)。 -/
theorem jointAtom_mul_eq (P Q : ConfirmProj E)
    (hcomm : ∀ x, P.M (Q.M x) = Q.M (P.M x)) (a a' b b' : Fin 2) :
    (side P.M a * side Q.M b) * (side P.M a' * side Q.M b')
      = (side P.M a * side P.M a') * (side Q.M b * side Q.M b') := by
  rw [mul_assoc (side P.M a) (side Q.M b) (side P.M a' * side Q.M b'),
    ← mul_assoc (side Q.M b) (side P.M a') (side Q.M b'),
    ← side_commute P Q hcomm a' b,
    mul_assoc (side P.M a') (side Q.M b) (side Q.M b')]
  exact (mul_assoc (side P.M a) (side P.M a') (side Q.M b * side Q.M b')).symm

/-- **T_谱μ0 (原子幂等)** jointAtom (a,b) 复合自身 = 自身——格点原子是合法确认投影。 -/
theorem jointAtom_mul_self (P Q : ConfirmProj E)
    (hcomm : ∀ x, P.M (Q.M x) = Q.M (P.M x)) (a b : Fin 2) :
    jointAtom P Q a b * jointAtom P Q a b = jointAtom P Q a b := by
  unfold jointAtom
  rw [jointAtom_mul_eq P Q hcomm a a b b, side_self_mul P.M P.idem a, side_self_mul Q.M Q.idem b]

/-- **T_谱μ0b (原子互斥·全对)** 格点不同 ⟹ 原子复合 = 0——
第四块 T_四3 两个代表对升格为全对 (乘积零统一路线的格点化)。 -/
theorem jointAtom_mul_eq_zero_of_ne (P Q : ConfirmProj E)
    (hcomm : ∀ x, P.M (Q.M x) = Q.M (P.M x)) (a a' b b' : Fin 2) (hne : a ≠ a' ∨ b ≠ b') :
    jointAtom P Q a b * jointAtom P Q a' b' = 0 := by
  unfold jointAtom
  rw [jointAtom_mul_eq P Q hcomm a a' b b']
  rcases hne with h | h
  · rw [side_mul_zero P.M P.idem a a' h, zero_mul]
  · rw [side_mul_zero Q.M Q.idem b b' h, mul_zero]

/-- **T_谱μ2 (归一)** 全格点原子和 = I——测量基完备性
(第四块"四块和=I"的测度形态: 2ⁿ 格 n=2 的 univ 情形)。 -/
theorem jointAtom_sum_univ (P Q : ConfirmProj E) :
    ∑ a : Fin 2, ∑ b : Fin 2, jointAtom P Q a b = 1 := by
  simp only [jointAtom]
  calc (∑ a : Fin 2, ∑ b : Fin 2, side P.M a * side Q.M b)
      = ∑ a : Fin 2, (side P.M a * ∑ b : Fin 2, side Q.M b) :=
        Finset.sum_congr rfl fun a _ =>
          (Finset.mul_sum Finset.univ (side Q.M) (side P.M a)).symm
    _ = (∑ a : Fin 2, side P.M a) * ∑ b : Fin 2, side Q.M b :=
        (Finset.sum_mul Finset.univ (side P.M) (∑ b : Fin 2, side Q.M b)).symm
    _ = 1 := by rw [side_sum, side_sum, one_mul]

/-- **T_谱μ3 (任意子集读出合法)** μ(s)² = μ(s)——任意格点子集的测度值仍是确认投影 (幂等)。
"测量基=谱族离散完整版"的测度级收口: 任意子集读数合法=补投影性的测度版。 -/
theorem jointMeasure_mul_self (P Q : ConfirmProj E)
    (hcomm : ∀ x, P.M (Q.M x) = Q.M (P.M x)) (s : Finset (Fin 2 × Fin 2)) :
    jointMeasure P Q s * jointMeasure P Q s = jointMeasure P Q s := by
  unfold jointMeasure
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_eq_single_of_mem p hp
    (fun q _ hq => by
      have hq' : ¬ (q = p) := hq
      rw [Prod.ext_iff] at hq'
      rcases eq_or_ne q.1 p.1 with h1 | h1
      · exact jointAtom_mul_eq_zero_of_ne P Q hcomm p.1 q.1 p.2 q.2
          (Or.inr fun hcon => hq' ⟨h1, hcon.symm⟩)
      · exact jointAtom_mul_eq_zero_of_ne P Q hcomm p.1 q.1 p.2 q.2 (Or.inl (Ne.symm h1)))]
  exact jointAtom_mul_self P Q hcomm p.1 p.2

/-- **T_谱μ4 (有限可加)** 不交并的测度 = 测度之和 (谱测度公理的有限形态)。 -/
theorem jointMeasure_sum_union (P Q : ConfirmProj E) (s t : Finset (Fin 2 × Fin 2))
    (hst : Disjoint s t) :
    jointMeasure P Q (s ∪ t) = jointMeasure P Q s + jointMeasure P Q t := by
  unfold jointMeasure
  exact Finset.sum_union hst

/-! ## 对易两面 (必要性自证 + 存在面 Mathlib 承重) -/

/-- 公共特征向量集合: 同时是 A 与 B 特征向量的全体。 -/
def commonEigenvec (A B : E →L[ℂ] E) : Set E := {v | ∃ a b : ℂ, A v = a • v ∧ B v = b • v}

/-- **T_谱G1a (必要性·有限维)** 存在公共特征正交基 ⟹ A∘B = B∘A——
"可同时确认 ⟹ 读数可并存"的定理级 (C4 要素对应表"测量基←约束族"必要性面)。 -/
theorem common_eigenbasis_commute {ι : Type*} [Fintype ι] (A B : E →L[ℂ] E)
    (e : OrthonormalBasis ι ℂ E)
    (hA : ∀ i, ∃ a : ℂ, A (e i) = a • e i) (hB : ∀ i, ∃ b : ℂ, B (e i) = b • e i) (x : E) :
    A (B x) = B (A x) := by
  choose a ha using hA
  choose b hb using hB
  have key : ∀ i, A (B (e i)) = B (A (e i)) := by
    intro i
    calc A (B (e i)) = A (b i • e i) := by rw [hb i]
      _ = b i • A (e i) := map_smul A (b i) (e i)
      _ = b i • (a i • e i) := by rw [ha i]
      _ = a i • (b i • e i) := by rw [smul_smul, smul_smul, mul_comm (b i) (a i)]
      _ = a i • B (e i) := by rw [hb i]
      _ = B (a i • e i) := (map_smul B (a i) (e i)).symm
      _ = B (A (e i)) := by rw [ha i]
  have expand : ∀ (T : E →L[ℂ] E) (y : E), T y = ∑ i, ⟪e i, y⟫_ℂ • T (e i) := by
    intro T y
    conv_lhs => rw [← e.sum_repr' y]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul T (⟪e i, y⟫_ℂ) (e i)
  have hsum : ∑ i, ⟪e i, x⟫_ℂ • A (e i) = A (∑ i, ⟪e i, x⟫_ℂ • e i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => (map_smul A (⟪e i, x⟫_ℂ) (e i)).symm
  calc A (B x) = A (∑ i, ⟪e i, x⟫_ℂ • B (e i)) := congrArg A (expand B x)
    _ = ∑ i, ⟪e i, x⟫_ℂ • A (B (e i)) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => map_smul A (⟪e i, x⟫_ℂ) (B (e i))
    _ = ∑ i, ⟪e i, x⟫_ℂ • B (A (e i)) := Finset.sum_congr rfl fun i _ => by rw [key i]
    _ = B (∑ i, ⟪e i, x⟫_ℂ • A (e i)) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => (map_smul B (⟪e i, x⟫_ℂ) (A (e i))).symm
    _ = B (A x) := by rw [hsum, e.sum_repr' x]

/-- **T_谱G1b (必要性·无限维)** 公共特征向量族张成稠密 ⟹ A∘B = B∘A——
连续谱/无限维形态: 不要求完备正交基, 只要求公共特征族张满 (稠密)。 -/
theorem commute_of_dense_common (A B : E →L[ℂ] E)
    (hd : Dense ((Submodule.span ℂ (commonEigenvec A B) : Submodule ℂ E) : Set E)) (x : E) :
    A (B x) = B (A x) := by
  have hD : ∀ y, B (A y) - A (B y) = (B.comp A - A.comp B) y := by
    intro y
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_comp, Function.comp_apply]
  have hzero : ∀ v ∈ commonEigenvec A B, (B.comp A - A.comp B) v = 0 := by
    rintro v ⟨a, b, ha, hb⟩
    simp only [← hD, ha, hb, map_smul, smul_smul, mul_comm a b, sub_self]
  have hle : Submodule.span ℂ (commonEigenvec A B) ≤ (B.comp A - A.comp B).ker := by
    rw [Submodule.span_le]
    intro v hv
    exact hzero v hv
  have hclosed : IsClosed (((B.comp A - A.comp B).ker : Submodule ℂ E) : Set E) :=
    ContinuousLinearMap.isClosed_ker (B.comp A - A.comp B)
  have hdk : ∀ y : E, y ∈ closure (((B.comp A - A.comp B).ker : Submodule ℂ E) : Set E) := by
    intro y
    have h2 : closure (↑(Submodule.span ℂ (commonEigenvec A B)) : Set E) ⊆
        closure (((B.comp A - A.comp B).ker : Submodule ℂ E) : Set E) :=
      closure_mono fun z hz => hle hz
    exact h2 (hd y)
  have hkerall : ∀ y : E, y ∈ ((B.comp A - A.comp B).ker : Submodule ℂ E) := by
    intro y
    have h3 : y ∈ (((B.comp A - A.comp B).ker : Submodule ℂ E) : Set E) := by
      rw [← hclosed.closure_eq]
      exact hdk y
    exact h3
  have h0 : (B.comp A - A.comp B) x = 0 := hkerall x
  exact (sub_eq_zero.mp ((hD x).trans h0)).symm

/-- **T_谱G2a (逆否·有限维)** 非对易 ⟹ 无公共特征正交基 (T_谱G1a 逆否)——
"读数不可并存 ⟹ 无同时确认的测量基"。 -/
theorem not_common_eigenbasis_of_noncommute {ι : Type*} [Fintype ι] (A B : E →L[ℂ] E)
    (e : OrthonormalBasis ι ℂ E) (hnc : ∃ x, A (B x) ≠ B (A x)) :
    ¬ ∀ i, (∃ a : ℂ, A (e i) = a • e i) ∧ (∃ b : ℂ, B (e i) = b • e i) := by
  intro h
  obtain ⟨x, hx⟩ := hnc
  exact hx (common_eigenbasis_commute A B e (fun i => (h i).1) (fun i => (h i).2) x)

/-- **T_谱G2b (逆否·无限维)** 非对易 ⟹ 公共特征族张成不稠密 (T_谱G1b 逆否)。 -/
theorem not_dense_common_of_noncommute (A B : E →L[ℂ] E) (hnc : ∃ x, A (B x) ≠ B (A x)) :
    ¬ Dense ((Submodule.span ℂ (commonEigenvec A B) : Submodule ℂ E) : Set E) := by
  intro hd
  obtain ⟨x, hx⟩ := hnc
  exact hx (commute_of_dense_common A B hd x)

/-- **T_谱G3 (存在面·对·Mathlib 承重登记)** 有限维内积空间上对易的对称算子对:
联合本征空间的并 = ⊤ (Mathlib JointEigenspace 承重·登记不重证)。 -/
theorem joint_eigenspace_top_of_commute {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (A B : F →ₗ[ℂ] F)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    (⨆ α : ℂ, ⨆ γ : ℂ, Module.End.eigenspace A α ⊓ Module.End.eigenspace B γ) = ⊤ :=
  LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hA hB hAB

/-- **T_谱G3b (存在面·族·Mathlib 承重登记)** 有限维上两两对易的对称算子族:
联合特征标空间的并 = ⊤ (同时可对角化·Mathlib JointEigenspace 承重)。 -/
theorem joint_eigenspace_top_of_pairwise_commute {ι F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (T : ι → F →ₗ[ℂ] F)
    (hT : ∀ i, (T i).IsSymmetric) (h : Pairwise (Commute on T)) :
    (⨆ χ : ι → ℂ, ⨅ i, Module.End.eigenspace (T i) (χ i)) = ⊤ :=
  LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT h

end DensityMath
