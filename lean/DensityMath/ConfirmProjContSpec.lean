/-
# 投影假设特例化第八块: 连续谱域读数结构 (投影值测度公理层) (T_谱C1-C9+划分, 2026-09-27)
对应: papers/对偶命题_投影假设特例化_第八块_连续谱域读数结构_v0.1.md
体系: 对偶命题线·投影假设形式级续块 —— 第五块挂账"连续谱/无限维谱测度"的
  集合代数层清偿 (候令清单执行线大件①·09-26 收敛 §31)

API 盘点复核 (2026-09-27·去幻·先于写码):
  - 第五块头注记 "spectralFamily|spectralMeasure 零命中 ⇒ 无 Mathlib 承重件"——
    本块全库 grep 复核属实 (spectralMeasure/spectralFamily/HasSpectralFamily/
    projectionValuedMeasure/pvm 零命中; Analysis/InnerProductSpace/ 下仅 Spectrum.lean
    无 Spectral.lean)——非 Fubini 块型"检索面不全"。
  - ⇒ 本块形态=自建公理结构+结构定理 (承重=集代数+CLM 环运算·Mathlib 基础件),
    非"Mathlib 承重+桥接"型; 无限维谱测度存在性 (一般自伴算子谱定理) 维持挂账。

预注册 (先于数据·本块定理清单):
  结构: ProjVM F——E : Set ℝ → (F →L[ℂ] F) 四公理 (empty/univ/add[不交可加]/idem[乘法幂等])
  T_谱C1 互补: E s + E sᶜ = 1
  T_谱C2 正交引理 (主引理): Disjoint s t → E s * E t = 0
    (证链: (P+Q)²=P+Q ⟹ PQ+QP=0 ⟹ 右乘/左乘 Q ⟹ PQ=QP ⟹ 2PQ=0 ⟹ PQ=0·Char 0·纯代数)
  T_谱C3 差可加: s ⊆ t → E t = E s + E (t ∖ s)
  T_谱C4 单调投影: s ⊆ t → E s * E t = E s
  T_谱C5 交公式 (本块主件): E (s ∩ t) = E s * E t
  T_谱C6 交换: E s * E t = E t * E s
  T_谱C7 原子正交: x ≠ y → E {x} * E {y} = 0
  T_谱C8 原子不动点 (离散读数出生点): E {x} ≠ 0 → ∃ x₀ ≠ 0, E {x} x₀ = x₀
  T_谱C9 无原子有限塌缩 (连续谱域主件): (∀ x, E {x} = 0) → ∀ 有限集 s, E ↑s = 0
    ——连续谱域单点读数不出生 (三体反面判例的正面定理化·配对核 r 失效的定理级形态)
  T_谱C10 三块划分归一 (Fubini 集合版): 两两不交 ∪ = univ ⟹ 和 = 1
边界 (如实标): σ-可加/无限维谱测度存在性/一般自伴算子谱定理——不在本块 (维持挂账);
  Born 权重无来源 (同前七块); 本块为集合代数层 (有限可加+幂等), 非 σ-代数层。
-/
import Mathlib

namespace ConfirmProjContSpec

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- 投影值测度 (公理形态·集合代数层): 谱集 ↦ 确认投影, 四公理 =
空集零 + 全域恒等 + 不交可加 + 乘法幂等。 -/
structure ProjVM (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] where
  /-- 谱测度: 集 ↦ 确认投影 (集合代数层·不筛 Borel) -/
  E : Set ℝ → (F →L[ℂ] F)
  /-- 空集: 零投影 -/
  empty : E ∅ = 0
  /-- 全域: 恒等 -/
  univ : E Set.univ = 1
  /-- 不交可加 -/
  add : ∀ s t : Set ℝ, Disjoint s t → E s + E t = E (s ∪ t)
  /-- 幂等 (乘法形态) -/
  idem : ∀ s : Set ℝ, E s * E s = E s

/-- 点态幂等辅助引理. -/
theorem idem_apply (P : ProjVM F) (s : Set ℝ) (v : F) :
    P.E s (P.E s v) = P.E s v := by
  have h := congrArg (fun A : F →L[ℂ] F => A v) (P.idem s)
  simpa [ContinuousLinearMap.mul_apply] using h

/-! ### 集合辅助 (自造·Mathlib 无对应件) -/

/-- s ∩ (t ∖ s) = ∅ 的 Disjoint 形态. -/
private theorem disj_sdiff (s t : Set ℝ) : Disjoint s (t \ s) := by
  rw [Set.disjoint_right]
  exact fun _a ha => ha.2

/-- s ∪ t ∖ s = t (s ⊆ t). -/
private theorem union_diff_cancel' {s t : Set ℝ} (hst : s ⊆ t) : s ∪ t \ s = t := by
  ext x
  simp only [Set.mem_union, Set.mem_diff]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact hst h
    · exact h
  · intro h
    by_cases hc : x ∈ s
    · exact Or.inl hc
    · exact Or.inr ⟨h, hc⟩

/-! ## T_谱C2 正交引理 (主引理·纯 Char-0 代数·不需要内积正性) -/

/-- T_谱C2 正交引理: 不交集的投影乘积为零。
证链: (P+Q)² = P+Q (不交可加+幂等) ⟹ PQ+QP = 0 ⟹ 右/左乘 Q ⟹ PQ = QP ⟹ 2PQ = 0 ⟹ PQ = 0. -/
theorem orth_mul (P : ProjVM F) {s t : Set ℝ} (hd : Disjoint s t) :
    P.E s * P.E t = 0 := by
  have hsum := P.add s t hd
  have hsq := P.idem (s ∪ t)
  rw [← hsum] at hsq
  -- hsq : (E s + E t) * (E s + E t) = E s + E t
  rw [add_mul, mul_add, mul_add, P.idem s, P.idem t] at hsq
  -- hsq : E s + (E s*E t + (E t*E s + E t)) = E s + E t (结合序近似)
  have h0 : P.E s * P.E t + P.E t * P.E s = 0 := by
    linear_combination (norm := abel_nf) hsq
  have r1 : (P.E s * P.E t + P.E t * P.E s) * P.E t = 0 := by rw [h0, zero_mul]
  have r2 : P.E t * (P.E s * P.E t + P.E t * P.E s) = 0 := by rw [h0, mul_zero]
  rw [add_mul] at r1
  rw [mul_add] at r2
  -- r1 : (A*B)*Q + (B*A)*Q = 0 → rw [mul_assoc, idem t] → A*B + (B*A)*Q = 0
  rw [mul_assoc, P.idem t] at r1
  -- r2 : Q*(A*B) + Q*(B*A) = 0 → (Q*A)*B + (Q*B)*A = 0 → idem t → (B*A)*B + B*A = 0
  rw [← mul_assoc, ← mul_assoc, P.idem t] at r2
  have hcomm : P.E s * P.E t = P.E t * P.E s := by
    linear_combination (norm := abel_nf) r1 - r2
  have h0' : P.E s * P.E t + P.E s * P.E t = 0 := by
    rw [← hcomm] at h0
    exact h0
  have h2 : (2:ℂ) • (P.E s * P.E t) = 0 := by
    rw [two_smul ℂ]
    exact h0'
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-! ## T_谱C1/C3/C4 可加性推论 -/

/-- T_谱C1 互补: E s + E sᶜ = 1. -/
theorem compl (P : ProjVM F) (s : Set ℝ) : P.E s + P.E sᶜ = 1 := by
  have hd : Disjoint s sᶜ := by
    rw [Set.disjoint_right]
    exact fun _a ha => ha
  have h := P.add s sᶜ hd
  rw [Set.union_compl_self, P.univ] at h
  exact h

/-- T_谱C3 差可加: s ⊆ t ⟹ E t = E s + E (t ∖ s). -/
theorem sdiff_add (P : ProjVM F) {s t : Set ℝ} (hst : s ⊆ t) :
    P.E t = P.E s + P.E (t \ s) := by
  have h := P.add s (t \ s) (disj_sdiff s t)
  rw [union_diff_cancel' hst] at h
  exact h.symm

/-- 交的右子集 (自造·Mathlib 该名已改 membership 形式). -/
private theorem inter_sub_right (s t : Set ℝ) : s ∩ t ⊆ t := fun _a ha => ha.2

/-- T_谱C4 单调投影: s ⊆ t ⟹ E s * E t = E s. -/
theorem mul_le (P : ProjVM F) {s t : Set ℝ} (hst : s ⊆ t) :
    P.E s * P.E t = P.E s := by
  calc P.E s * P.E t = P.E s * (P.E s + P.E (t \ s)) := by rw [sdiff_add P hst]
    _ = P.E s * P.E s + P.E s * P.E (t \ s) := by rw [mul_add]
    _ = P.E s + 0 := by rw [P.idem s, orth_mul P (disj_sdiff s t)]
    _ = P.E s := by simp

/-! ## T_谱C5 交公式 (本块主件) 与 T_谱C6 交换 -/

/-- T_谱C5 交公式 (主件): E (s ∩ t) = E s * E t——窗逻辑的核:
"确认到交集 = 两个窗确认的复合". -/
theorem inter_mul (P : ProjVM F) (s t : Set ℝ) :
    P.E (s ∩ t) = P.E s * P.E t := by
  have hd : Disjoint (s ∩ t) (s ∩ tᶜ) := by
    rw [Set.disjoint_right]
    exact fun _a ha hmem =>
      (Set.notMem_of_mem_compl (Set.mem_of_mem_inter_right ha))
        (Set.mem_of_mem_inter_right hmem)
  have hu : s ∩ t ∪ s ∩ tᶜ = s := by
    rw [← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]
  have hEs : P.E s = P.E (s ∩ t) + P.E (s ∩ tᶜ) := by
    have h := P.add (s ∩ t) (s ∩ tᶜ) hd
    rw [hu] at h
    exact h.symm
  have hsub : P.E (s ∩ t) * P.E t = P.E (s ∩ t) :=
    mul_le P (inter_sub_right s t)
  have hdm : Disjoint (s ∩ tᶜ) t := by
    rw [Set.disjoint_right]
    exact fun _a ha hbad =>
      (Set.notMem_of_mem_compl (Set.mem_of_mem_inter_right hbad)) ha
  have hzero : P.E (s ∩ tᶜ) * P.E t = 0 := orth_mul P hdm
  rw [hEs, add_mul, hsub, hzero, add_zero]

/-- T_谱C6 交换: 投影值测度两两交换 (交公式的直接推论). -/
theorem mul_comm' (P : ProjVM F) (s t : Set ℝ) :
    P.E s * P.E t = P.E t * P.E s := by
  rw [← inter_mul P s t, ← inter_mul P t s, Set.inter_comm]

/-! ## T_谱C7/C8 原子层 (离散读数的出生点) -/

/-- T_谱C7 原子正交: x ≠ y ⟹ 单点原子投影互零. -/
theorem atom_orth (P : ProjVM F) {x y : ℝ} (hxy : x ≠ y) :
    P.E {x} * P.E {y} = 0 :=
  orth_mul P (Set.disjoint_singleton.mpr hxy)

/-- T_谱C8 原子不动点 (离散读数出生点): 原子投影非零 ⟹ 有非零不动点
——配对核 T_对4 (值域=不动点集) 在原子层的实例:
原子非零 ⟺ 离散读数在该点出生. -/
theorem atom_fixed (P : ProjVM F) {x : ℝ} (h : P.E {x} ≠ 0) :
    ∃ x₀ : F, x₀ ≠ 0 ∧ P.E {x} x₀ = x₀ := by
  have hv : ∃ v : F, P.E {x} v ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact h (ContinuousLinearMap.ext fun v => hall v)
  obtain ⟨v, hv⟩ := hv
  exact ⟨P.E {x} v, hv, idem_apply P {x} v⟩

/-! ## T_谱C9 连续谱域主件 (无原子 ⟹ 有限集零·离散读数不出生) -/

/-- T_谱C9 无原子有限塌缩 (连续谱域主件): 全部单点原子为零 ⟹ 任意有限集上
投影为零——**连续谱域单点读数不出生** (三体反面判例"约束精确但离散读数不显"
的正面定理化·配对核 r : X → ℕ 在此域失效的定理级形态). -/
theorem finite_null (P : ProjVM F) (hno : ∀ x : ℝ, P.E {x} = 0) (s : Finset ℝ) :
    P.E (s : Set ℝ) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using P.empty
  | insert x s hx ih =>
    have hcoe : ((insert x s : Finset ℝ) : Set ℝ) = (↑s ∪ {x} : Set ℝ) := by
      rw [Finset.coe_insert, ← Set.singleton_union, Set.union_comm]
    have hd : Disjoint (↑s : Set ℝ) ({x} : Set ℝ) := by
      rw [Set.disjoint_singleton_right]
      exact hx
    have h := P.add (↑s : Set ℝ) ({x} : Set ℝ) hd
    rw [ih, hno x, zero_add, ← hcoe] at h
    exact h.symm

/-! ## T_谱C10 三块划分归一 (Fubini 集合版) -/

/-- T_谱C10 三块划分归一: 两两不交且并 = 全域 ⟹ 读出和 = 1
(读出完备性·Fubini 件 T_F2 的集合代数版). -/
theorem three_part (P : ProjVM F) (a b c : Set ℝ)
    (hab : Disjoint a b) (hac : Disjoint a c) (hbc : Disjoint b c)
    (hun : a ∪ b ∪ c = Set.univ) :
    P.E a + P.E b + P.E c = 1 := by
  have habc : Disjoint (a ∪ b) c := Set.disjoint_union_left.mpr ⟨hac, hbc⟩
  have heq : (a ∪ b) ∪ c = Set.univ := hun
  have h2 := P.add (a ∪ b) c habc
  rw [heq, P.univ] at h2
  rw [P.add a b hab]
  exact h2

#print axioms ConfirmProjContSpec.idem_apply
#print axioms ConfirmProjContSpec.orth_mul
#print axioms ConfirmProjContSpec.compl
#print axioms ConfirmProjContSpec.sdiff_add
#print axioms ConfirmProjContSpec.mul_le
#print axioms ConfirmProjContSpec.inter_mul
#print axioms ConfirmProjContSpec.mul_comm'
#print axioms ConfirmProjContSpec.atom_orth
#print axioms ConfirmProjContSpec.atom_fixed
#print axioms ConfirmProjContSpec.finite_null
#print axioms ConfirmProjContSpec.three_part

end ConfirmProjContSpec
