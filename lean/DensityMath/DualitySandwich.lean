/-
# 对偶表 c 行: A'3 夹逼判据读数域完整版 (T_S1-T_S6, 2026-09-26)
对应: papers/对偶表_c行_描述约定层对接_v0.1.md §五.3 (三行尾部唯一残留·中件清偿)
体系: 描述约定层第五成员 A'3 (夹逼判据: 维数约定 = 完备读出下界 × 最简编码上界的等号点)
  在读数域的完整形式化 + 与 c 行核 (T_R2 重定标变换律 / T_R3 约定固定点) 的对接:
  夹逼等号点是约定重定标的不变量 (T_S6) —— 维数读数与数值读数分层相容.

语义锚 (体系层·不进形式层):
  - 读出族 = 读出空间中的向量族; 完备 = 张成 (少了丢结构), 最简 = 线性无关 (多了冗余);
  - 等号点 = 完备∧最简 (即基) 的基数 = finrank —— A'3 "夹逼取等号点"的定理级形态;
  - 重定标 κᵢ ≠ 0 = 单位重定标 (T_R2 读数变换律) 作用在读出族上: 数值随框架变,
    而完备/最简/等号点全部不动 (T_S4-T_S6) —— 维数读数是约定重定标的不变量,
    与约定固定点 (T_R3) 分层相容: 约定锚定读数框架, 不改变框架内的维数约定.
边界 (如实标): 线性读出域 (dimension_construction §3.2 的结构前提) —— 非线性读出域
  不在本块; 翻译层纪律: 定理级=抽象结构内.
-/
import Mathlib

open Set Submodule

namespace DualitySandwich

variable (K : Type*) {V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V]

/-- 完备读出族 (A'3 右翼前提): 张成整个读出空间 —— 少了丢结构. -/
def Complete (f : ι → V) : Prop := ⊤ ≤ span K (range f)

/-- T_S1 完备下界 (右翼): 完备读出族基数 ≥ finrank —— "少了丢结构"的界.
    证明: 构造满射 (c ↦ ∑ cᵢ·fᵢ) 并用维数在满射下的单调性. -/
theorem complete_lower [Fintype ι] {f : ι → V} (hspan : Complete K f) :
    Module.finrank K V ≤ Fintype.card ι := by
  classical
  have hsp : ⊤ ≤ span K (range f) := hspan
  let F : (ι → K) →ₗ[K] V :=
    { toFun := fun c => ∑ i, c i • f i
      map_add' := by
        intro c d
        show ∑ i, (c i + d i) • f i = ∑ i, c i • f i + ∑ i, d i • f i
        simp only [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro r c; simp [Finset.smul_sum, smul_smul] }
  have hsurj : Function.Surjective F := by
    intro x
    have hx : x ∈ span K (range f) := hsp (mem_top)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    exact ⟨c, hc⟩
  have h1 := LinearMap.finrank_le_finrank_of_surjective hsurj
  rwa [Module.finrank_fintype_fun_eq_card] at h1

/-- T_S2 最简上界 (左翼): 最简 (线性无关) 读出族基数 ≤ finrank —— "多了冗余"的界. -/
theorem simple_upper [Fintype ι] {f : ι → V} (hli : LinearIndependent K f) :
    Fintype.card ι ≤ Module.finrank K V :=
  hli.fintype_card_le_finrank

/-- T_S3 夹逼等号点: 完备 ∧ 最简 ⟹ 基数 = finrank —— A'3 "取等号点"的定理级形态
    (完备且最简的读出族即基, 基数=维数: 完备读出=最简读出). -/
theorem eq_point [Fintype ι] {f : ι → V} (hspan : Complete K f)
    (hli : LinearIndependent K f) : Fintype.card ι = Module.finrank K V := by
  have hb : Module.Basis ι K V := Module.Basis.mk hli hspan
  exact (Module.finrank_eq_card_basis hb).symm

/-- T_S4 最简的重定标不变: 各分量乘 κᵢ ≠ 0 不改线性无关 ——
    T_R2 读数重定标作用在最简族上, 冗余结构不动. -/
theorem rescale_simple [Fintype ι] {f : ι → V} {κ : ι → K} (hκ : ∀ i, κ i ≠ 0)
    (hli : LinearIndependent K f) : LinearIndependent K (fun i => κ i • f i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h2 : ∑ j, (g j * κ j) • f j = 0 := by
    simp_rw [← smul_smul]; exact hg
  rcases mul_eq_zero.mp
    ((Fintype.linearIndependent_iff.mp hli) (fun j => g j * κ j) h2 i) with h | h
  · exact h
  · exact absurd h (hκ i)

/-- T_S5 完备的重定标不变: 各分量乘 κᵢ ≠ 0 不改张成 ——
    T_R2 读数重定标作用在完备族上, 覆盖能力不动. -/
theorem rescale_complete [Fintype ι] {f : ι → V} {κ : ι → K} (hκ : ∀ i, κ i ≠ 0)
    (hspan : Complete K f) : Complete K (fun i => κ i • f i) := by
  have hsp : ⊤ ≤ span K (range f) := hspan
  have heq : span K (range (fun i => κ i • f i)) = span K (range f) := by
    refine le_antisymm (span_le.2 ?_) (span_le.2 ?_)
    · rintro y ⟨i, rfl⟩
      exact smul_mem _ _ (subset_span ⟨i, rfl⟩)
    · rintro y ⟨i, rfl⟩
      have hfi : f i = (κ i)⁻¹ • (κ i • f i) := by
        rw [smul_smul, inv_mul_cancel₀ (hκ i), one_smul]
      rw [hfi]
      exact smul_mem _ _ (subset_span ⟨i, rfl⟩)
  show ⊤ ≤ span K (range (fun i => κ i • f i))
  rw [heq]
  exact hsp

/-- T_S6 等号点的约定不变性: 完备∧最简族重定标后仍完备∧最简且基数不变 ——
    夹逼等号点 (维数读数) 是约定重定标 (T_R2 变换律) 的不变量. c 行桥:
    数值读数随框架变 (T_R2), 维数等号点不动 —— 分层相容于约定固定点 (T_R3). -/
theorem eq_point_rescale [Fintype ι] {f : ι → V} {κ : ι → K} (hκ : ∀ i, κ i ≠ 0)
    (hspan : Complete K f) (hli : LinearIndependent K f) :
    Complete K (fun i => κ i • f i)
      ∧ LinearIndependent K (fun i => κ i • f i)
      ∧ Fintype.card ι = Module.finrank K V :=
  ⟨rescale_complete K hκ hspan, rescale_simple K hκ hli, eq_point K hspan hli⟩

#print axioms DualitySandwich.complete_lower
#print axioms DualitySandwich.simple_upper
#print axioms DualitySandwich.eq_point
#print axioms DualitySandwich.rescale_simple
#print axioms DualitySandwich.rescale_complete
#print axioms DualitySandwich.eq_point_rescale

end DualitySandwich
