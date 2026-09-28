/-
# 对偶表 c 行: 描述约定层对接核 (T_C1-T_C4, 2026-09-26)
对应: papers/对偶表_c行_描述约定层对接_v0.1.md
体系: 对偶表元约束三行结构抽象 (§四) 的 c 行续块——"与描述约定层第五成员的形式对接".
对接语义 (映射·非 A' 公理重述——A'1-A'4 的 Lean 件在第五成员论文附录 A 在案):
  - T_R2 (重定标变换律·DualityRatio) ↔ A'1 约定层自由: 单位重定标=框架选择, 不内含于量;
  - 比值读数不变 (T_R1) ↔ A'3 无损层: 比值区分跨框架保真 (零失真层·可通约);
  - **本块新核 = A'4 塌维判据的读数版**: "区分的维持以承诺为资源" 的算子化——
    T_C1 绝对区分随框架缩放 (框架依赖) / T_C2 比值区分承诺无关 (无损层) /
    T_C3 无承诺塌缩 (重定标不变的绝对读出必常数——承诺退场则区分退场) /
    T_C4 承诺恢复区分 (承诺在场则区分在).
  - c 行实测锚: SI 2019 约定固定 c=299792458 m/s (精确值由定义给) = 一次数值承诺 ——
    单位框架 (米/秒) 的区分由承诺维持 (A'4 语义); κ₀=299792458.
边界 (如实标): 本块为读数结构层的最小核, 不重述 A' 公理本身 (维度约定生成机制的
  形式化在第五成员论文); λ 群同态等深层结构维持候令; 翻译层纪律.
-/
import Mathlib

namespace DualityConvention

/-- 读出框架族: r_κ(q) = f(q)/κ —— f = 量族上的基准读出, κ = 框架参数 (单位). -/
noncomputable def readout (f : ℝ → ℝ) (κ q : ℝ) : ℝ := f q / κ

/-- T_C1 绝对区分框架依赖: 两量读数差随 κ 缩放 —— 绝对区分是框架内读数 (A'1 语义). -/
theorem diff_scale (f : ℝ → ℝ) (κ q₁ q₂ : ℝ) :
    readout f κ q₁ - readout f κ q₂ = (f q₁ - f q₂) / κ := by
  simp [readout, sub_div]

/-- T_C2 比值区分承诺无关: 两量读数比与 κ 无关 —— 比值区分在无损层 (A'3 语义·T_R1 特例形态). -/
theorem ratio_indep (f : ℝ → ℝ) (κ q₁ q₂ : ℝ) (hκ : κ ≠ 0) (hq : f q₂ ≠ 0) :
    readout f κ q₁ / readout f κ q₂ = f q₁ / f q₂ := by
  simp only [readout]
  field_simp

/-- T_C3 无承诺塌缩: 若读出对所有重定标不变 (κ 未承诺·框架悬空), 则它在非零量上恒定 ——
    区分退场 (A'4 "承诺退场则区分退场" 的算子化). -/
theorem no_promise_collapse (f : ℝ → ℝ)
    (hinvar : ∀ (κ q : ℝ), κ ≠ 0 → f q = f (q * κ)) (q : ℝ) (hq : q ≠ 0) :
    f q = f 1 := by
  have h := hinvar q 1 hq
  simpa [mul_one] using h.symm

/-- T_C4 承诺恢复区分: 给定承诺 κ₀ (≠0), 非退化量对的框架读数区分在 ——
    承诺在场则区分在 (A'4 前向·SI 2019 约定固定 c 的读数语义). -/
theorem promise_restores (f : ℝ → ℝ) (κ₀ q₁ q₂ : ℝ) (hκ : κ₀ ≠ 0) (hdiff : f q₁ ≠ f q₂) :
    readout f κ₀ q₁ ≠ readout f κ₀ q₂ := by
  intro h
  apply hdiff
  have h1 : readout f κ₀ q₁ - readout f κ₀ q₂ = (f q₁ - f q₂) / κ₀ :=
    diff_scale f κ₀ q₁ q₂
  have h3 : (f q₁ - f q₂) / κ₀ = 0 := by rw [← h1, h, sub_self]
  rw [div_eq_zero_iff, sub_eq_zero] at h3
  rcases h3 with h3 | h3
  · exact h3
  · exact absurd h3 hκ

#print axioms DualityConvention.diff_scale
#print axioms DualityConvention.ratio_indep
#print axioms DualityConvention.no_promise_collapse
#print axioms DualityConvention.promise_restores

end DualityConvention
