/-
# 投影假设特例化第六块: 联合谱族一般 n (2ⁿ 格·Fintype 约束族) (2026-09-25)
对应: 第五块挂账"2ⁿ 格一般 n"(papers/对偶命题_投影假设特例化_第五块_一般谱测度_v0.1.md §五.1)
体系: 对偶命题 C4 严格化第六块——n 条两两对易约束的联合谱族 (一般 n)

★API 盘点 (先于写码·grep 留痕·Mathlib v4.33.1):
  - ★Finset.prod 定义在 CommMonoid 上 (BigOperators/Group/Finset/Defs.lean:68)——
    CLM (非交换 Monoid) 上 `∏` 不可用! 非交换乘积 = Finset.noncommProd
    (Data/Finset/NoncommProd.lean:247·Pairwise Commute 义务)
  - 承重件在案: noncommProd_commute (元素×乘积交换) / noncommProd_insert_of_notMem /
    noncommProd_cons / noncommProd_empty (全 @[simp])——自证件仅剩乘积幂等 (cons 归纳)
  - 格点和 Fubini (∑_v ∏_i f i (v i) = ∏_i ∑_a f i a): prod_univ_sum 零命中
    ⇒ 归一的一般 n 形态挂账 (逐约束归一 side_sum 已在第五块·n=2 归一已在案)
本块交付 (原子三性质+测度读出合法性·一般 n):
  T_族1 原子幂等 / T_族2 原子互斥 (全对·分歧点归零) / T_族3 复合分类
  T_族4 任意子集读出合法 μ(s)²=μ(s) / T_族5 有限可加
边界 (如实标): 一般 n 格点和=I = Fubini 挂账; 证明结构=分歧点归零·非全乘积重排。
-/
import Mathlib
import DensityMath.ConfirmProjSpectral

open scoped InnerProductSpace
open scoped Function

namespace DensityMath

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## 一般 Monoid 非交换乘积引理 (自证·cons 归纳·universal comm) -/

/-- **非交换乘积幂等**: 逐点幂等 + 两两交换 ⟹ 乘积幂等
(comm 为 universal 变元——Prop 论证不相关性使各处 comm 证明项可互换)。 -/
theorem noncommProd_mul_self {β : Type*} [Monoid β] {ι : Type*} (s : Finset ι) (f : ι → β)
    (hidem : ∀ i, f i * f i = f i) (hcomm : ∀ i j, i ≠ j → Commute (f i) (f j))
    (comm : (s : Set ι).Pairwise fun x y => Commute (f x) (f y)) :
    s.noncommProd f comm * s.noncommProd f comm = s.noncommProd f comm := by
  classical
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a t ha ih =>
    have hPA : Commute (f a)
        (t.noncommProd f (comm.mono fun x hx => Finset.mem_cons.2 (Or.inr hx))) :=
      Finset.noncommProd_commute t f _ (f a) fun x hx =>
        hcomm a x fun h => ha (h ▸ hx)
    rw [Finset.noncommProd_cons t a f ha comm]
    show (f a * t.noncommProd f _) * (f a * t.noncommProd f _)
      = f a * t.noncommProd f _
    calc (f a * t.noncommProd f _) * (f a * t.noncommProd f _)
        = f a * ((t.noncommProd f _ * f a) * t.noncommProd f _) := by
          rw [mul_assoc, ← mul_assoc (t.noncommProd f _) (f a) (t.noncommProd f _)]
      _ = f a * ((f a * t.noncommProd f _) * t.noncommProd f _) := by rw [hPA]
      _ = (f a * f a) * (t.noncommProd f _ * t.noncommProd f _) := by
          rw [mul_assoc (f a) (t.noncommProd f _) (t.noncommProd f _),
            ← mul_assoc (f a) (f a)
              (t.noncommProd f _ * t.noncommProd f _)]
      _ = f a * t.noncommProd f _ := by
          rw [hidem a,
            ih (comm.mono fun x hx => Finset.mem_cons.2 (Or.inr hx))]

/-! ## 一般 n 条对易约束的联合谱族 -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- **交叉对易 (族版)**: 不同约束的侧算子两两可交换 (第五块 side_commute 的族化)。 -/
theorem side_commuteN {P : ι → ConfirmProj E}
    (hcomm : ∀ i j, i ≠ j → ∀ x, (P i).M ((P j).M x) = (P j).M ((P i).M x))
    {i j : ι} (hij : i ≠ j) (a b : Fin 2) :
    side (P i).M a * side (P j).M b = side (P j).M b * side (P i).M a :=
  side_commute (P i) (P j) (hcomm i j hij) a b

omit [Fintype ι] [DecidableEq ι] in
/-- 同一格点族的侧算子两两交换 (i=j 平凡 / i≠j 交叉对易)。 -/
theorem side_pairwise_commute {P : ι → ConfirmProj E}
    (hcomm : ∀ i j, i ≠ j → ∀ x, (P i).M ((P j).M x) = (P j).M ((P i).M x))
    (v : ι → Fin 2) (i j : ι) :
    Commute (side (P i).M (v i)) (side (P j).M (v j)) := by
  unfold Commute
  rcases eq_or_ne i j with rfl | hij
  · rfl
  · exact side_commuteN hcomm hij _ _

omit [Fintype ι] [DecidableEq ι] in
/-- 全格点族的 Pairwise 交换义务 (comm 槽的承重件——声明处吸收 lambda-对-Pairwise 检查)。 -/
theorem side_pairwise_set {P : ι → ConfirmProj E}
    (hcomm : ∀ i j, i ≠ j → ∀ x, (P i).M ((P j).M x) = (P j).M ((P i).M x))
    (v : ι → Fin 2) (s : Finset ι) :
    (↑s : Set ι).Pairwise (Commute on fun i => side (P i).M (v i)) :=
  fun x _ y _ _ => side_pairwise_commute hcomm v x y

/-- **联合谱原子 (一般 n)**: 格点 v : ι → Fin 2 的读出算子 = 侧算子族的非交换乘积——
n 条对易约束 ⟹ 2ⁿ 格谱族的格点化 (格点集 = Fintype (ι → Fin 2))。 -/
def jointAtomN (P : ι → ConfirmProj E)
    (hcomm : ∀ i j, i ≠ j → ∀ x, (P i).M ((P j).M x) = (P j).M ((P i).M x))
    (v : ι → Fin 2) : E →L[ℂ] E :=
  Finset.univ.noncommProd (fun i => side (P i).M (v i))
    (side_pairwise_set hcomm v Finset.univ)

/-- **T_族1 (原子幂等·一般 n)**: jointAtomN v 复合自身 = 自身——格点原子是合法确认投影。 -/
theorem jointAtomN_mul_self (P : ι → ConfirmProj E)
    (hcomm : ∀ i j, i ≠ j → ∀ x, (P i).M ((P j).M x) = (P j).M ((P i).M x)) (v : ι → Fin 2) :
    jointAtomN P hcomm v * jointAtomN P hcomm v = jointAtomN P hcomm v := by
  unfold jointAtomN
  exact noncommProd_mul_self Finset.univ (fun i => side (P i).M (v i))
    (fun i => side_self_mul (P i).M (P i).idem (v i))
    (fun i j _ => side_pairwise_commute hcomm v i j)
    (side_pairwise_set hcomm v Finset.univ)

/-- **原子互斥·泛化形态** (cons 归纳): 有限集含分歧点 ⟹ 两原子积 = 0——
t-积的 comm 一律用 mono 显式形态 (与 noncommProd_cons 输出同构)。 -/
theorem jointAtomN_mul_eq_zero_of_mem_diff (P : ι → ConfirmProj E)
    (hcomm : ∀ i j, i ≠ j → ∀ x, (P i).M ((P j).M x) = (P j).M ((P i).M x))
    {s : Finset ι} {v w : ι → Fin 2} :
    (∃ i ∈ s, v i ≠ w i) →
    s.noncommProd (fun i => side (P i).M (v i)) (side_pairwise_set hcomm v s)
      * s.noncommProd (fun i => side (P i).M (w i)) (side_pairwise_set hcomm w s) = 0 := by
  induction s using Finset.cons_induction_on with
  | empty =>
    intro h
    obtain ⟨i, hi, _⟩ := h
    exact absurd hi (by simp)
  | cons a t ha ih =>
    show (∃ i ∈ Finset.cons a t ha, v i ≠ w i) →
      (Finset.cons a t ha).noncommProd (fun i => side (P i).M (v i))
        (side_pairwise_set hcomm v (Finset.cons a t ha))
      * (Finset.cons a t ha).noncommProd (fun i => side (P i).M (w i))
        (side_pairwise_set hcomm w (Finset.cons a t ha)) = 0
    intro hdiff
    obtain ⟨i, hi, hne⟩ := hdiff
    -- t-积 (cons 展开形态·mono comm)
    have hax : ∀ x ∈ t, x ≠ a := fun x hx hax' => ha (hax' ▸ hx)
    have hXz : ∀ z : Fin 2, side (P a).M z
        * (t.noncommProd (fun x => side (P x).M (v x))
          ((side_pairwise_set hcomm v (insert a t)).mono (Finset.subset_insert a t)))
      = (t.noncommProd (fun x => side (P x).M (v x))
          ((side_pairwise_set hcomm v (insert a t)).mono (Finset.subset_insert a t)))
        * side (P a).M z :=
      fun z => Finset.noncommProd_commute t _ _ _ fun x hx =>
        (side_commuteN hcomm (hax x hx) (v x) z).symm
    by_cases hva : v a = w a
    · -- a 非分歧: 分歧点在 t
      have hdiff_t : ∃ j ∈ t, v j ≠ w j := by
        rcases Finset.mem_cons.mp hi with rfl | hm
        · exact absurd hva hne
        · exact ⟨i, hm, hne⟩
      rw [Finset.noncommProd_cons t a (fun x => side (P x).M (v x)) ha _,
        Finset.noncommProd_cons t a (fun x => side (P x).M (w x)) ha _,
        hva]
      show (side (P a).M (w a)
            * t.noncommProd (fun x => side (P x).M (v x))
              ((side_pairwise_set hcomm v (insert a t)).mono (Finset.subset_insert a t)))
        * (side (P a).M (w a)
            * t.noncommProd (fun x => side (P x).M (w x))
              ((side_pairwise_set hcomm w (insert a t)).mono (Finset.subset_insert a t)))
        = 0
      calc (side (P a).M (w a)
            * t.noncommProd (fun x => side (P x).M (v x))
              ((side_pairwise_set hcomm v (insert a t)).mono (Finset.subset_insert a t)))
          * (side (P a).M (w a)
              * t.noncommProd (fun x => side (P x).M (w x))
                ((side_pairwise_set hcomm w (insert a t)).mono (Finset.subset_insert a t)))
          = side (P a).M (w a)
              * ((t.noncommProd (fun x => side (P x).M (v x))
                  ((side_pairwise_set hcomm v (insert a t)).mono (Finset.subset_insert a t))
                * side (P a).M (w a))
                * t.noncommProd (fun x => side (P x).M (w x))
                  ((side_pairwise_set hcomm w (insert a t)).mono (Finset.subset_insert a t))) := by
              rw [mul_assoc, ← mul_assoc (t.noncommProd (fun x => side (P x).M (v x))
                ((side_pairwise_set hcomm v (insert a t)).mono (Finset.subset_insert a t)))
                (side (P a).M (w a))
                (t.noncommProd (fun x => side (P x).M (w x))
                ((side_pairwise_set hcomm w (insert a t)).mono (Finset.subset_insert a t)))]
        _ = side (P a).M (w a)
              * ((side (P a).M (w a)
                  * t.noncommProd (fun x => side (P x).M (v x))
                    ((side_pairwise_set hcomm v (insert a t)).mono (Finset.subset_insert a t)))
                * t.noncommProd (fun x => side (P x).M (w x))
                  ((side_pairwise_set hcomm w (insert a t)).mono (Finset.subset_insert a t))) := by
              rw [hXz (w a)]
        _ = (side (P a).M (w a) * side (P a).M (w a))
              * (t.noncommProd (fun x => side (P x).M (v x))
                  ((side_pairwise_set hcomm v (insert a t)).mono (Finset.subset_insert a t))
                * t.noncommProd (fun x => side (P x).M (w x))
                  ((side_pairwise_set hcomm w (insert a t)).mono (Finset.subset_insert a t))) := by
              rw [mul_assoc (side (P a).M (w a))
                (t.noncommProd (fun x => side (P x).M (v x))
                ((side_pairwise_set hcomm v (insert a t)).mono (Finset.subset_insert a t)))
                (t.noncommProd (fun x => side (P x).M (w x))
                ((side_pairwise_set hcomm w (insert a t)).mono (Finset.subset_insert a t))),
                ← mul_assoc (side (P a).M (w a)) (side (P a).M (w a))
                (t.noncommProd (fun x => side (P x).M (v x))
                ((side_pairwise_set hcomm v (insert a t)).mono (Finset.subset_insert a t))
                * t.noncommProd (fun x => side (P x).M (w x))
                ((side_pairwise_set hcomm w (insert a t)).mono (Finset.subset_insert a t)))]
        _ = 0 := by
              rw [side_self_mul (P a).M (P a).idem (w a),
                ih hdiff_t,
                mul_zero]
    · -- a 即分歧点: side_a 互斥直接归零
      rw [Finset.noncommProd_cons t a (fun x => side (P x).M (v x)) ha _,
        Finset.noncommProd_cons t a (fun x => side (P x).M (w x)) ha _]
      show (side (P a).M (v a)
            * t.noncommProd (fun x => side (P x).M (v x))
              ((side_pairwise_set hcomm v (insert a t)).mono (Finset.subset_insert a t)))
        * (side (P a).M (w a)
            * t.noncommProd (fun x => side (P x).M (w x))
              ((side_pairwise_set hcomm w (insert a t)).mono (Finset.subset_insert a t)))
        = 0
      calc (side (P a).M (v a)
            * t.noncommProd (fun x => side (P x).M (v x))
              ((side_pairwise_set hcomm v (insert a t)).mono (Finset.subset_insert a t)))
          * (side (P a).M (w a)
              * t.noncommProd (fun x => side (P x).M (w x))
                ((side_pairwise_set hcomm w (insert a t)).mono (Finset.subset_insert a t)))
          = side (P a).M (v a)
              * ((t.noncommProd (fun x => side (P x).M (v x))
                  ((side_pairwise_set hcomm v (insert a t)).mono (Finset.subset_insert a t))
                * side (P a).M (w a))
                * t.noncommProd (fun x => side (P x).M (w x))
                  ((side_pairwise_set hcomm w (insert a t)).mono (Finset.subset_insert a t))) := by
              rw [mul_assoc, ← mul_assoc (t.noncommProd (fun x => side (P x).M (v x))
                ((side_pairwise_set hcomm v (insert a t)).mono (Finset.subset_insert a t)))
                (side (P a).M (w a))
                (t.noncommProd (fun x => side (P x).M (w x))
                ((side_pairwise_set hcomm w (insert a t)).mono (Finset.subset_insert a t)))]
        _ = side (P a).M (v a)
              * ((side (P a).M (w a)
                  * t.noncommProd (fun x => side (P x).M (v x))
                    ((side_pairwise_set hcomm v (insert a t)).mono (Finset.subset_insert a t)))
                * t.noncommProd (fun x => side (P x).M (w x))
                  ((side_pairwise_set hcomm w (insert a t)).mono (Finset.subset_insert a t))) := by
              rw [hXz (w a)]
        _ = (side (P a).M (v a) * side (P a).M (w a))
              * (t.noncommProd (fun x => side (P x).M (v x))
                  ((side_pairwise_set hcomm v (insert a t)).mono (Finset.subset_insert a t))
                * t.noncommProd (fun x => side (P x).M (w x))
                  ((side_pairwise_set hcomm w (insert a t)).mono (Finset.subset_insert a t))) := by
              rw [mul_assoc (side (P a).M (w a))
                (t.noncommProd (fun x => side (P x).M (v x))
                ((side_pairwise_set hcomm v (insert a t)).mono (Finset.subset_insert a t)))
                (t.noncommProd (fun x => side (P x).M (w x))
                ((side_pairwise_set hcomm w (insert a t)).mono (Finset.subset_insert a t))),
                ← mul_assoc (side (P a).M (v a)) (side (P a).M (w a))
                (t.noncommProd (fun x => side (P x).M (v x))
                ((side_pairwise_set hcomm v (insert a t)).mono (Finset.subset_insert a t))
                * t.noncommProd (fun x => side (P x).M (w x))
                ((side_pairwise_set hcomm w (insert a t)).mono (Finset.subset_insert a t)))]
        _ = 0 := by
              rw [side_mul_zero (P a).M (P a).idem (v a) (w a) hva, zero_mul]

theorem jointAtomN_mul_eq_zero_of_ne (P : ι → ConfirmProj E)
    (hcomm : ∀ i j, i ≠ j → ∀ x, (P i).M ((P j).M x) = (P j).M ((P i).M x))
    {v w : ι → Fin 2} (hne : v ≠ w) :
    jointAtomN P hcomm v * jointAtomN P hcomm w = 0 := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hne
  exact jointAtomN_mul_eq_zero_of_mem_diff P hcomm ⟨i₀, Finset.mem_univ i₀, hi₀⟩

/-- **T_族3 (复合分类)**: v = w 时幂等 / v ≠ w 时归零——二值一侧。 -/
theorem jointAtomN_mul (P : ι → ConfirmProj E)
    (hcomm : ∀ i j, i ≠ j → ∀ x, (P i).M ((P j).M x) = (P j).M ((P i).M x))
    (v w : ι → Fin 2) :
    jointAtomN P hcomm v * jointAtomN P hcomm w
      = if v = w then jointAtomN P hcomm v else 0 := by
  by_cases h : v = w
  · subst h
    rw [if_pos rfl, jointAtomN_mul_self P hcomm v]
  · rw [if_neg h, jointAtomN_mul_eq_zero_of_ne P hcomm h]

/-- **联合格点测度 (一般 n)**: 任意格点子集 ↦ 原子和。 -/
def jointMeasureN (P : ι → ConfirmProj E)
    (hcomm : ∀ i j, i ≠ j → ∀ x, (P i).M ((P j).M x) = (P j).M ((P i).M x))
    (s : Finset (ι → Fin 2)) : E →L[ℂ] E :=
  ∑ v ∈ s, jointAtomN P hcomm v

/-- **T_族4 (任意子集读出合法·一般 n)**: μ(s)² = μ(s)——
任意格点子集的测度值仍是确认投影 (补投影性测度版·2ⁿ 格一般 n)。 -/
theorem jointMeasureN_mul_self (P : ι → ConfirmProj E)
    (hcomm : ∀ i j, i ≠ j → ∀ x, (P i).M ((P j).M x) = (P j).M ((P i).M x))
    (s : Finset (ι → Fin 2)) :
    jointMeasureN P hcomm s * jointMeasureN P hcomm s = jointMeasureN P hcomm s := by
  unfold jointMeasureN
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_eq_single_of_mem p hp (fun q _ hq => by
    rw [jointAtomN_mul P hcomm p q, if_neg fun h1 => hq h1.symm])]
  exact jointAtomN_mul_self P hcomm p

/-- **T_族5 (有限可加·一般 n)**: 不交并的测度 = 测度之和。 -/
theorem jointMeasureN_sum_union (P : ι → ConfirmProj E)
    (hcomm : ∀ i j, i ≠ j → ∀ x, (P i).M ((P j).M x) = (P j).M ((P i).M x))
    (s t : Finset (ι → Fin 2)) (hst : Disjoint s t) :
    jointMeasureN P hcomm (s ∪ t) = jointMeasureN P hcomm s + jointMeasureN P hcomm t := by
  unfold jointMeasureN
  exact Finset.sum_union hst

end DensityMath
