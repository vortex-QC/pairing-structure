/-
# 对偶表 α 行: RG 流偏差谱离散核 (T_β1-T_β5, 2026-09-26)
对应: papers/对偶表_α行_RG流偏差谱_v0.1.md
体系: 对偶表元约束三行结构抽象 (对偶表_元约束三行_结构抽象_v0.1.md §四) 的 α 行续块——
  "耦合空间上的标度群作用具体模型"的中件落地: RG 流的离散序列代数形态.

语义锚 (体系层·不进形式层):
  - 乘性偏差律 δ_{n+1}=λ·δ_n = 不动点线性化的离散领头阶 (标准 RG 结构:
    δg ∝ β'(g*)·δg) —— 形式层只做序列代数, 不宣称具体体系的 β 函数数值;
  - λ = 偏差特征值 = "耦合偏差谱"的承载 (α 行语义: 偏差=对不动点的偏离,
    对称性=R'=1 截面·偏差=力比偏离);
  - T_β2 的基准步 m 自由 = "α 即固定 RG 流上的能标读数选择 (约定参数化)"
    (9-25 判读级) 的序列代数形态: 读数比值由步差决定·基准=约定.
  - 实测锚 (观测栏·一手核验在案): Parker 2018 α 测量链全比值化 (三行抽象档 §一).
边界 (如实标): 连续流/对数跑动 (λ=1 边际的修正项) 不进本块 (T_β4 只给恒定形态);
  翻译层纪律: 定理级=抽象结构内.
2026-09-26 续: T_β6/T_β7 排斥侧 (|λ|>1 UV 侧) 补齐——三分类 (收敛/边际/排斥) 定理级闭合.
-/
import Mathlib

namespace DualityRG

/-- 离散 RG 流轨道: 不动点 g* + 偏差序列 δ_n = g_n − g* + 乘性偏差律
    δ_{n+1} = λ·δ_n (不动点线性化的离散领头阶·最小假设). -/
structure RGOrbit where
  lam : ℝ
  delta : ℕ → ℝ
  hmult : ∀ n, delta (n + 1) = lam * delta n

/-- T_β1 偏差乘性幂律: δ_n = λⁿ·δ₀ (乘性律的封闭解·n 归纳). -/
theorem delta_pow (R : RGOrbit) (n : ℕ) : R.delta n = R.lam ^ n * R.delta 0 := by
  induction n with
  | zero => simp
  | succ k ih => rw [R.hmult, ih, pow_succ]; ring

/-- T_β2 偏差比 (步差形态): 自基准 m 起, δ_{m+k}/δ_m = λᵏ ——
    读数比值由能标步差决定·基准步 m 自由 (读数位置=约定·序列代数形态). -/
theorem delta_ratio_shift (R : RGOrbit) (m k : ℕ) (hm : R.delta m ≠ 0) :
    R.delta (m + k) / R.delta m = R.lam ^ k := by
  induction k with
  | zero => simpa using div_self hm
  | succ j ih =>
    have h1 : R.delta (m + (j + 1)) = R.lam * R.delta (m + j) := by
      rw [← Nat.add_assoc]; exact R.hmult (m + j)
    rw [h1, mul_div_assoc, ih, pow_succ']

/-- T_β3 偏差比 (一般形态): n = m+(n−m) 咬合步差形态. -/
theorem delta_ratio (R : RGOrbit) (m n : ℕ) (hmn : m ≤ n) (hm : R.delta m ≠ 0) :
    R.delta n / R.delta m = R.lam ^ (n - m) := by
  have h : n = m + (n - m) := (Nat.add_sub_cancel' hmn).symm
  conv_lhs => rw [h]
  exact delta_ratio_shift R m (n - m) hm

/-- T_β4 吸引分类 (IR 侧): |λ| < 1 ⟹ 偏差趋于零 —— 不动点 IR 吸引的离散形态. -/
theorem attractor (R : RGOrbit) (habs : |R.lam| < 1) :
    Filter.Tendsto R.delta Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun n : ℕ => R.lam ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_iff.mpr habs
  have h2 : (fun n : ℕ => R.delta n) = fun n : ℕ => R.lam ^ n * R.delta 0 :=
    funext (delta_pow R)
  show Filter.Tendsto (fun n : ℕ => R.delta n) Filter.atTop (nhds 0)
  rw [h2]
  have h4 := h1.mul_const (R.delta 0)
  simpa using h4

/-- T_β5 边际位置: λ = 1 ⟹ 偏差恒定 —— 边际算符 (对数跑动位置) 的零特征形态. -/
theorem marginal (R : RGOrbit) (h : R.lam = 1) (n : ℕ) : R.delta n = R.delta 0 := by
  rw [delta_pow R n, h, one_pow, one_mul]

/-- T_β6 排斥侧无界 (UV 侧): |λ| > 1 ∧ δ₀ ≠ 0 ⟹ |δ_n| → ∞ ——
    不动点 UV 排斥的离散形态 (偏差跑飞; Bernoulli 下界 |λ|ⁿ ≥ 1+n(|λ|−1) 压过线性). -/
theorem repulsive (R : RGOrbit) (habs : 1 < |R.lam|) (h0 : R.delta 0 ≠ 0) :
    Filter.Tendsto (fun n => |R.delta n|) Filter.atTop Filter.atTop := by
  have hq : (0:ℝ) < |R.lam| - 1 := by linarith
  have hc : (0:ℝ) < (|R.lam| - 1) * |R.delta 0| :=
    mul_pos hq (abs_pos.mpr h0)
  have hbern : ∀ n : ℕ, (1:ℝ) + n * (|R.lam| - 1) ≤ (|R.lam|) ^ n := by
    intro n
    have h := one_add_mul_le_pow (a := |R.lam| - 1) (by linarith) n
    rwa [show (1:ℝ) + (|R.lam| - 1) = |R.lam| by ring] at h
  have h1 : ∀ n : ℕ, |R.delta n| = (|R.lam|) ^ n * |R.delta 0| := by
    intro n; rw [delta_pow R n, abs_mul, abs_pow]
  have hexpand : ∀ r : ℝ, r * |R.delta 0| ≤ ((1:ℝ) + r) * |R.delta 0| := by
    intro r; ring_nf; linarith [abs_nonneg (R.delta 0)]
  have hpow : ∀ n : ℕ, ((|R.lam| - 1) * |R.delta 0|) * (n:ℝ) ≤ |R.delta n| := by
    intro n
    calc ((|R.lam| - 1) * |R.delta 0|) * (n:ℝ)
        = (n:ℝ) * (|R.lam| - 1) * |R.delta 0| := by ring
      _ ≤ ((1:ℝ) + (n:ℝ) * (|R.lam| - 1)) * |R.delta 0| := hexpand _
      _ ≤ ((|R.lam|) ^ n) * |R.delta 0| :=
        mul_le_mul_of_nonneg_right (hbern n) (abs_nonneg (R.delta 0))
      _ = |R.delta n| := (h1 n).symm
  exact Filter.tendsto_atTop_mono hpow
    (tendsto_natCast_atTop_atTop.const_mul_atTop hc)

/-- T_β7 排斥侧唯一收敛轨道: |λ| > 1 ∧ δ_n → 0 ⟹ δ₀ = 0 ——
    不动点在 UV 侧只容纳不动点自身 (排斥的判据形态: 收敛⟹起点即不动点). -/
theorem repulsive_unique (R : RGOrbit) (habs : 1 < |R.lam|)
    (h : Filter.Tendsto R.delta Filter.atTop (nhds 0)) : R.delta 0 = 0 := by
  by_contra h0
  have hdiv := repulsive R habs h0
  have hev : ∀ᶠ n in Filter.atTop, |R.delta n| < 1 := by
    have hm := Metric.tendsto_nhds.mp h (1:ℝ) (by norm_num)
    simpa [Real.dist_eq] using hm
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N1, hN1⟩ := hev
  have hgt := hdiv.eventually (Filter.eventually_gt_atTop 1)
  rw [Filter.eventually_atTop] at hgt
  obtain ⟨N2, hN2⟩ := hgt
  have hA := hN1 (max N1 N2) (le_max_left _ _)
  have hB := hN2 (max N1 N2) (le_max_right _ _)
  exact absurd hA (not_lt.2 hB.le)

#print axioms DualityRG.delta_pow
#print axioms DualityRG.delta_ratio
#print axioms DualityRG.attractor
#print axioms DualityRG.marginal
#print axioms DualityRG.repulsive
#print axioms DualityRG.repulsive_unique

section ContFlow

/- 连续流块 (T_γ1-T_γ5·2026-09-26 晚轻件): α 行档 "形态选择" 段的续件 ——
   连续化的李群结构 = 一参数群最小形式 (群律/比值/边际) + 离散化嵌入
   (等步采样恢复 RGOrbit·分类由 γ 符号承载·吸引/排斥经 T_β4/T_β6 继承).
   边界 (如实标): 连续时间的实时吸引/排斥 (Real tendsto) 不在本块 —— 采样版分类承重;
   λ 数值留白维持. -/

/-- 连续流读数: 偏差随能标 t 指数跑动 δ(t) = x·exp(γ·t) (乘性律连续版·一参数群轨道). -/
noncomputable def flowAt (γ t x : ℝ) : ℝ := x * Real.exp (γ * t)

/-- T_γ1 一参数群律 (李群结构核): 流的复合 = 参数相加 φ_s∘φ_t = φ_{s+t}
    (含单位 φ_0=id 与逆 φ_{−t}·半群律形式). -/
theorem flow_group_law (γ s t x : ℝ) :
    flowAt γ s (flowAt γ t x) = flowAt γ (s + t) x := by
  show (x * Real.exp (γ * t)) * Real.exp (γ * s) = x * Real.exp (γ * (s + t))
  rw [mul_assoc, ← Real.exp_add, mul_add, add_comm (γ * t) (γ * s)]

/-- T_γ2 流比值读数: 两能标读数比 = exp(γ·(t₂−t₁)) —— 读数比值由能标差决定
    (T_β3 的连续版: 基准 t₁ 自由·读数位置=约定). -/
theorem flow_ratio (γ t₁ t₂ d₀ : ℝ) (hd : d₀ ≠ 0) :
    flowAt γ t₂ d₀ / flowAt γ t₁ d₀ = Real.exp (γ * (t₂ - t₁)) := by
  have h1 : flowAt γ t₂ d₀ / flowAt γ t₁ d₀ = Real.exp (γ * t₂) / Real.exp (γ * t₁) := by
    simp only [flowAt]
    rw [mul_div_mul_left _ _ hd]
  rw [h1, mul_sub, Real.exp_sub]

/-- T_γ3 离散化嵌入: 连续流等步采样 (Δt 步长) 的轨道是 RGOrbit 实例 ——
    连续流是离散轨道的母体 (κ = exp(γ·Δt) = 每步特征值). -/
theorem sample_embedding (γ Δt d₀ : ℝ) :
    ∃ orb : RGOrbit, orb.lam = Real.exp (γ * Δt)
      ∧ ∀ n : ℕ, orb.delta n = d₀ * Real.exp (γ * Δt) ^ n := by
  refine ⟨⟨Real.exp (γ * Δt), fun n => d₀ * Real.exp (γ * Δt) ^ n, ?_⟩, rfl, fun _ => rfl⟩
  intro n
  rw [pow_succ]
  ring

/-- T_γ4 边际=零流: γ=0 ⟹ 流恒定 (T_β5 的连续对偶: λ=1 ⟺ γ=0). -/
theorem flow_marginal (γ t x : ℝ) (h : γ = 0) : flowAt γ t x = x := by
  rw [flowAt, h, zero_mul, Real.exp_zero, mul_one]

/-- T_γ5a 采样轨道 IR 吸引: γ<0 ⟹ 采样偏差轨道趋于零 (经 T_β4: |κ|<1). -/
theorem sample_attracts (γ Δt d₀ : ℝ) (hγ : γ < 0) (hΔ : 0 < Δt) :
    Filter.Tendsto (fun n : ℕ => d₀ * Real.exp (γ * Δt) ^ n) Filter.atTop (nhds 0) := by
  let horb : RGOrbit := ⟨Real.exp (γ * Δt), fun n => d₀ * Real.exp (γ * Δt) ^ n, by
    intro n; rw [pow_succ]; ring⟩
  have hlam : horb.lam = Real.exp (γ * Δt) := rfl
  have habs : |horb.lam| < 1 := by
    rw [hlam, abs_of_pos (Real.exp_pos (γ * Δt)), Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos hγ hΔ
  show Filter.Tendsto horb.delta Filter.atTop (nhds 0)
  exact attractor horb habs

/-- T_γ5b 采样轨道 UV 排斥: 0<γ ⟹ 采样偏差轨道无界 (经 T_β6: |κ|>1·δ₀≠0 时). -/
theorem sample_repels (γ Δt d₀ : ℝ) (hγ : 0 < γ) (hΔ : 0 < Δt) (hd : d₀ ≠ 0) :
    Filter.Tendsto (fun n : ℕ => |d₀ * Real.exp (γ * Δt) ^ n|) Filter.atTop Filter.atTop := by
  let horb : RGOrbit := ⟨Real.exp (γ * Δt), fun n => d₀ * Real.exp (γ * Δt) ^ n, by
    intro n; rw [pow_succ]; ring⟩
  have hlam : horb.lam = Real.exp (γ * Δt) := rfl
  have habs : 1 < |horb.lam| := by
    rw [hlam, abs_of_pos (Real.exp_pos (γ * Δt)), Real.one_lt_exp_iff]
    exact mul_pos hγ hΔ
  have h0 : horb.delta 0 ≠ 0 := by
    intro hcon
    apply hd
    have hz : horb.delta 0 = d₀ := by
      show d₀ * Real.exp (γ * Δt) ^ 0 = d₀
      simp
    rw [hz] at hcon
    exact hcon
  show Filter.Tendsto (fun n => |horb.delta n|) Filter.atTop Filter.atTop
  exact repulsive horb habs h0

#print axioms DualityRG.flow_group_law
#print axioms DualityRG.flow_ratio
#print axioms DualityRG.sample_embedding
#print axioms DualityRG.flow_marginal
#print axioms DualityRG.sample_attracts
#print axioms DualityRG.sample_repels

end ContFlow

end DualityRG
