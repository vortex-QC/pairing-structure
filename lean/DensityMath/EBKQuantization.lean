/-
# EBK 定理化第一块: 自洽读数谱结构 (T_EBK.1-T_EBK.5, 2026-09-25)
对应: papers/EBK定理化_立项_v0.1.md §四
体系: 对偶命题线定理化 (构造数学标准 §四.2 定理认证形态)

语义锚 (体系层, 不进形式层——数学形态层/体系语义层分离见总标准 §五):
  - 读数载体 J: 相空间作用量 (守恒=确认必要条件, 对偶命题立项档 §六.3)
  - 斜率 k=2π/ħ: 元约束=确认动作的代价 (作用量维, 对偶表 ħ 行)
  - 截距 β=μπ/2+bπ: π 约束的读数位置 (转折点=约束边界, 每边界 π/2, 判读级)
  - 单值自洽: 绕圈一周读数复原 = 显化幂等性 (M∘M=M) 的循环形态
数学内容 (纯结构): 线性相位转移 + 单值自洽 ⟹ 等差谱;
  谱距 = 2π/k 与截距无关 (π 项不进谱距 = π/ħ 分工定理);
  确认读出 = floor 型 P 投影 (幂等 + 非恒等 = 有损)。
-/
import Mathlib

namespace DensityMath

/-- 辅助: 2π ≠ 0 (相位自洽条件的非退化基)。 -/
theorem two_pi_ne_zero : (2 : ℝ) * Real.pi ≠ 0 := by
  have h1 : (0 : ℝ) < Real.pi := Real.pi_pos
  linarith

/-! ## 确认循环结构 -/

/-- 确认循环: 线性相位转移结构。
`k` = 作用量→相位转移率 (体系语义 k=2π/ħ, 元约束 ħ=确认代价, 正性=确认有代价);
`β` = 相位修正项 (体系语义 β=μπ/2+bπ, π 约束在转折点的读数位置)。 -/
structure ConfirmLoop where
  k : ℝ
  β : ℝ
  k_pos : 0 < k

/-- 相位积累: Φ(J) = k·J + β (转移线性——公理形态)。 -/
def phase (c : ConfirmLoop) (J : ℝ) : ℝ := c.k * J + c.β

/-- 单值自洽 (幂等的循环形态): 绕圈一周相位复原至 2π 的整数倍。 -/
def SelfConsistent (c : ConfirmLoop) (J : ℝ) : Prop :=
  ∃ n : ℤ, phase c J = 2 * Real.pi * n

/-- 可确认读数谱: 满足单值自洽的作用量值集。 -/
def EBKSpec (c : ConfirmLoop) : Set ℝ := {J : ℝ | SelfConsistent c J}

/-- 谱点参数化: J_n = (2π·n − β)/k。 -/
noncomputable def specPoint (c : ConfirmLoop) (n : ℤ) : ℝ := (2 * Real.pi * n - c.β) / c.k

/-- 谱点的相位恰为 2π·n (格点回归——自洽的定点性)。 -/
theorem phase_specPoint (c : ConfirmLoop) (n : ℤ) :
    phase c (specPoint c n) = 2 * Real.pi * n := by
  simp only [phase, specPoint]
  field_simp [c.k_pos.ne']
  ring

/-! ## T_EBK.1 谱的刻画 -/

/-- **定理 T_EBK.1 (谱的显式刻画)** 可确认读数 ⟺ 谱点:
J ∈ 谱 ⟺ ∃ n∈ℤ, J = (2πn−β)/k ——谱由整数索引唯一参数化。 -/
theorem spectrum_iff (c : ConfirmLoop) (J : ℝ) :
    J ∈ EBKSpec c ↔ ∃ n : ℤ, J = specPoint c n := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simp only [specPoint]
    rw [eq_div_iff c.k_pos.ne']
    simp only [phase] at hn
    linarith
  · rintro ⟨n, rfl⟩
    exact ⟨n, phase_specPoint c n⟩

/-- **定理 T_EBK.4 (谱可数)** 谱 = specPoint 的像——谱与 ℤ 等势。
体系语义: 对偶命题 §六.4 实数谱系分层 (演化可显化确定值至多可数谱) 的 EBK 实例化。 -/
theorem spectrum_range (c : ConfirmLoop) :
    EBKSpec c = Set.range (specPoint c) := by
  ext J
  rw [spectrum_iff c J]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, hn.symm⟩
  · rintro ⟨n, hn⟩; exact ⟨n, hn.symm⟩

/-- 谱点参数化的单射 (谱无重合——真可数而非有限重复)。 -/
theorem specPoint_injective (c : ConfirmLoop) {n m : ℤ} (h : specPoint c n = specPoint c m) :
    n = m := by
  simp only [specPoint] at h
  field_simp [c.k_pos.ne'] at h
  have hEq : (2 : ℝ) * Real.pi * (n : ℝ) = (2 : ℝ) * Real.pi * (m : ℝ) := by linarith
  have hcast : (n : ℝ) = (m : ℝ) := mul_right_injective₀ two_pi_ne_zero hEq
  exact Int.cast_injective hcast

/-! ## T_EBK.2 谱距定理 (π 项不进谱距) -/

/-- **定理 T_EBK.2 (谱距 = 2π/k)** 相邻谱点差 = 2π/k——与 β 无关。
体系语义: 谱距由元约束 ħ 单独决定——π 修正项不进谱距 (π/ħ 分工的谱距面)。 -/
theorem spectrum_gap (c : ConfirmLoop) (n : ℤ) :
    specPoint c (n + 1) - specPoint c n = 2 * Real.pi / c.k := by
  simp only [specPoint, Int.cast_add, Int.cast_one]
  field_simp [c.k_pos.ne']
  ring

/-- **定理 T_EBK.2' (谱距由 k 唯一决定)** 同 k 不同 β 的两循环谱距相等。
体系语义: 换约束 (转折点数 μ 变) 不动谱距; 换元约束 (ħ 变) 才动谱距。 -/
theorem spectrum_gap_only_k {c c' : ConfirmLoop} (hk : c.k = c'.k) (n : ℤ) :
    specPoint c (n + 1) - specPoint c n = specPoint c' (n + 1) - specPoint c' n := by
  rw [spectrum_gap, spectrum_gap, hk]

/-- 任意两谱点之差 = 谱距 × 整数 (谱是 ħ 格 × ℤ 的仿射格)。 -/
theorem spectrum_point_diff (c : ConfirmLoop) (n m : ℤ) :
    specPoint c n - specPoint c m = (2 * Real.pi / c.k) * (n - m : ℤ) := by
  simp only [specPoint, Int.cast_sub]
  field_simp [c.k_pos.ne']
  ring

/-! ## T_EBK.3 分工分离 (π 管位置, ħ 管格距) -/

/-- **定理 T_EBK.3 (平移结构)** 截距变化只平移谱: β → β+δ 把谱平移 −δ/k。
体系语义: π 修正项 (转折点数变化) 平移谱不改格结构——π 管位置不侵格距。 -/
theorem spectrum_shift (c : ConfirmLoop) (δ : ℝ) :
    EBKSpec { c with β := c.β + δ } = (fun J => J - δ / c.k) '' EBKSpec c := by
  ext J
  show (∃ n : ℤ, phase { c with β := c.β + δ } J = 2 * Real.pi * n) ↔
      ∃ J', SelfConsistent c J' ∧ J' - δ / c.k = J
  simp only [phase, SelfConsistent]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨J + δ / c.k, ⟨n, ?_⟩, by ring⟩
    have h2 : c.k * (J + δ / c.k) = c.k * J + δ := by
      field_simp [c.k_pos.ne']
    rw [h2]
    linarith
  · rintro ⟨J', ⟨n, hn⟩, hEq⟩
    refine ⟨n, ?_⟩
    have hJ' : J' = J + δ / c.k := by linarith
    subst hJ'
    have h2 : c.k * (J + δ / c.k) = c.k * J + δ := by
      field_simp [c.k_pos.ne']
    rw [h2] at hn
    linarith

/-! ## T_EBK.5 确认动作的 P 型投影实现 -/

/-- 确认读出算子: 连续作用量向下投影到谱格 (floor 型 P 投影)。
体系语义: C4 档「确认动作取 P 型投影形态」的显式实现——读出=投影到可确认格。 -/
noncomputable def confirmRead (c : ConfirmLoop) (J : ℝ) : ℝ :=
  specPoint c ⌊ phase c J / (2 * Real.pi) ⌋

/-- **定理 T_EBK.5a (读出落谱)** 确认读出的像在谱上——任何作用量值一经读出即落格。 -/
theorem confirmRead_mem (c : ConfirmLoop) (J : ℝ) : confirmRead c J ∈ EBKSpec c :=
  ⟨⌊ phase c J / (2 * Real.pi) ⌋, phase_specPoint c _⟩

/-- **定理 T_EBK.5b (幂等)** 确认读出是幂等自映射——读出一次后再读不变 (M∘M=M)。
体系语义: 显化算子幂等性 (静的显化定义 4.1) 在 EBK 循环上的实例化。 -/
theorem confirmRead_idem (c : ConfirmLoop) (J : ℝ) :
    confirmRead c (confirmRead c J) = confirmRead c J := by
  have hPhase : phase c (confirmRead c J)
      = 2 * Real.pi * (⌊ phase c J / (2 * Real.pi) ⌋ : ℝ) :=
    phase_specPoint c _
  have hdiv : (2 * Real.pi * (⌊ phase c J / (2 * Real.pi) ⌋ : ℝ)) / (2 * Real.pi)
      = (⌊ phase c J / (2 * Real.pi) ⌋ : ℝ) := by
    rw [div_eq_iff two_pi_ne_zero]
    ring
  show specPoint c ⌊ phase c (confirmRead c J) / (2 * Real.pi) ⌋
      = specPoint c ⌊ phase c J / (2 * Real.pi) ⌋
  rw [hPhase, hdiv, Int.floor_intCast]

/-- **定理 T_EBK.5c (非恒等=有损)** 确认读出非恒等——半格点被拉到格上。
体系语义: 幂等且非恒等 = 显化算子 (P 型·有损)——「读出吞动」(定理 4.5 语义) 的投影实现。 -/
theorem confirmRead_lossy (c : ConfirmLoop) :
    ∃ J, confirmRead c J ≠ J := by
  have hgap : specPoint c 1 - specPoint c 0 = 2 * Real.pi / c.k := by
    simpa using spectrum_gap c 0
  have hpos : (0 : ℝ) < 2 * Real.pi / c.k :=
    div_pos (by have h1 : (0 : ℝ) < Real.pi := Real.pi_pos; linarith) c.k_pos
  refine ⟨(specPoint c 0 + specPoint c 1) / 2, ?_⟩
  have h0 : phase c (specPoint c 0) = 0 := by simpa using phase_specPoint c 0
  have h1 : phase c (specPoint c 1) = 2 * Real.pi := by simpa using phase_specPoint c 1
  have hmid : phase c ((specPoint c 0 + specPoint c 1) / 2) = Real.pi := by
    have expand : phase c ((specPoint c 0 + specPoint c 1) / 2)
        = (phase c (specPoint c 0) + phase c (specPoint c 1)) / 2 := by
      simp only [phase]
      field_simp
      ring
    rw [expand, h0, h1]
    ring
  have hf : ⌊(1 / 2 : ℝ)⌋ = 0 := by
    rw [Int.floor_eq_iff]
    norm_num
  have hread : confirmRead c ((specPoint c 0 + specPoint c 1) / 2) = specPoint c 0 := by
    simp only [confirmRead, hmid]
    rw [show Real.pi / (2 * Real.pi) = (1 / 2 : ℝ) from by
      rw [div_eq_iff two_pi_ne_zero]
      ring]
    rw [hf]
  intro hEq
  have hB : specPoint c 0 - specPoint c 1 = 0 := by linarith
  have hgt : specPoint c 1 - specPoint c 0 > 0 := by linarith
  linarith

end DensityMath
