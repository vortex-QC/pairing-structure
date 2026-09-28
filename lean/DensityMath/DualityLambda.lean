/-
# 对偶表 Λ 行纯锚解析版: 可通约谱外判定定理 (2026-09-26)
对应: papers/对偶表_Λ行_纯锚解析版_v0.1.md (元约束三行差距表 Λ 项清偿·大件)
体系: P8 归约测试 (1323 单项式组合零命中·数值级·纯锚带第 3 例) 的解析化——
  零命中从"枚举观测"升为"区间定理+证书": 细线分解 (整数骨架) + 有理区间角点证书,
  对输入区间的 ALL 值成立 (非逐点) —— 数值枚举的精度依赖被结构证明替代.

语义锚 (体系层·不进形式层):
  - 生成元: x = m_Pl/m_p (跨层比·P9 在案) × α (电磁层耦合) × 10^m (十进制容差因子);
    目标: t = log10(ρ_Λ/ρ_Pl) (Planck 2018/DES 2018 无量纲分数报告·立项档 §八④).
  - P8: 15% 容差 (log10 距离 0.060698) 零命中 + 随机基线 31.3% —— 纯锚带第 3 例
    (TOV/SMBH/Λ). 本文件证明: 证书区间内 ALL 值失配 ≥ 1/16 = 0.0625 > 0.060698
    (阈值有效性由证书脚本 mpmath 兑现·数据_Lambda行纯锚解析_v0.1.json).
  - 解析结构: D = J + w —— 整数骨架 J = 19n−2k+m+123 承担全部整数部分;
    |J| ≥ 4 三角带判离; |J| ≤ 3 细带内 k 被钉死为 n 的仿射函数 (k 盒 ⟹ 每案 ≤2 候选),
    最近失配 (n,k,m)=(−7,−5,0) 落 J=0 线, |D|=0.1675=2.76δ —— 失配机理=
    细线斜率 S=2a−19b≈−2.371 与 n*=−7.14 的离整距离 (0.14×1.19≈0.17).
边界 (如实标): 区间宽度 = P8 输入通值的有效数字宽度 (非全物理不确定度外推);
  定理是抽象结构内命题 (翻译层纪律); 零新增物理测量值; 阈值 1/16 与 15% 容差的
  对接 (log10(1.15) < 1/16) 是数值事实 (mpmath 60 位·脚本兑现) 不进形式层.
-/
import Mathlib

open Set

namespace DualityLambda

variable (a b c : ℝ)

/-- 通约谱单项式的 log10 读数: 生成元读数 u=log10 x, v=log10 α 与十进制因子
    (log10 10^m = m·log10 10 = m·1, 已内嵌) 的单项式组合. -/
def monoLog (u v : ℝ) (n k m : ℤ) : ℝ := n * u + k * v + m

/-- 纯锚 (可通约谱外): 目标 t 与全部单项式组合的 log10 距离 ≥ δ.
    体系语义: 纯锚带的形式定义 (P1 推导等级三分"纯锚带"的形式层成员) ——
    目标量不可由生成元单项式谱在容差 δ 内通约 (跨层不可通约的判定形态). -/
def PureAnchor (u v t : ℝ) (N : ℕ) (δ : ℝ) : Prop :=
  ∀ n k : ℤ, n.natAbs ≤ N → k.natAbs ≤ N → ∀ m : ℤ, m.natAbs ≤ 1 →
    δ ≤ |monoLog u v n k m - t|

/-- 辅助: natAbs 界的实数 cast. -/
private lemma cast_abs_le (n : ℤ) (N : ℕ) (h : n.natAbs ≤ N) :
    (n:ℝ) ≤ (N:ℝ) ∧ -(n:ℝ) ≤ (N:ℝ) := by
  have h' : -(N:ℤ) ≤ n ∧ n ≤ (N:ℤ) := by omega
  have h1 : (n:ℝ) ≤ (N:ℝ) := by exact_mod_cast h'.2
  have h2 : ((-n:ℤ):ℝ) ≤ (N:ℝ) := by exact_mod_cast (by omega : (-n:ℤ) ≤ (N:ℤ))
  rw [Int.cast_neg] at h2
  exact ⟨h1, h2⟩

/-- 辅助: 乘积的盒界 —— |x|≤10, y∈[lo,hi], 0≤lo ⟹ |x*y| ≤ 10·hi. -/
private lemma scale_le (x : ℤ) (y lo hi : ℝ) (hx : (x:ℝ) ≤ 10 ∧ -(x:ℝ) ≤ 10)
    (hy : lo ≤ y ∧ y ≤ hi) (hlo : 0 ≤ lo) :
    (x:ℝ)*y ≤ 10*hi ∧ -((x:ℝ)*y) ≤ 10*hi := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hy0 : (0:ℝ) ≤ y := by linarith
  constructor
  · by_cases h0 : (0:ℝ) ≤ (x:ℝ)
    · have t1 : (x:ℝ)*y ≤ 10*y := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 10 - (x:ℝ)) hy0]
      linarith
    · push_neg at h0
      have t1 : (x:ℝ)*y ≤ 0 := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ -(x:ℝ)) hy0]
      linarith
  · by_cases h0 : (0:ℝ) ≤ (x:ℝ)
    · have t1 : 0 ≤ (x:ℝ)*y := by nlinarith [mul_nonneg h0 hy0]
      linarith
    · push_neg at h0
      have t1 : -((x:ℝ)*y) ≤ 10*y := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 10 + (x:ℝ)) hy0]
      linarith


/-- T_Λ3_01 细带案 (J=-3, m=-1): k 钉死 (2k=19n+-1+123−(-3)),
    k 盒 ⟹ n∈[-7,-6], 每候选角点证书 (区间角点由生成器预验·JSON 在案). -/
private lemma thin_jm3_m1 (n k : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10)
    (hj : 19*n - 2*k + (-1:ℤ) + 123 = (-3:ℤ))
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |((n:ℝ))*(19+a) + ((k:ℝ))*(-(2+b)) + ((-1:ℤ):ℝ) + 123 - c| := by
  have hnZ : n ≤ 10 ∧ -n ≤ 10 := by omega
  have hkZ : k ≤ 10 ∧ -k ≤ 10 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  have hW1 : n ≤ -6 := by omega
  have hW2 : -7 ≤ n := by omega
  interval_cases n
  ·
    have hk2 : 2*k = -8 := by omega
    have hkv : k = -4 := by omega
    subst hkv
    set E : ℝ := (((-7:ℤ):ℝ))*(19+a) + (((-4:ℤ):ℝ))*(-(2+b)) + ((-1:ℤ):ℝ) + 123 - c with hE
    norm_num at hE
    ring_nf at hE
    have hside : E ≤ -(1:ℝ)/16 := by linarith
    calc (1:ℝ)/16 ≤ -(E) := by linarith
      _ ≤ |E| := neg_le_abs E
  ·
    have hk2 : 2*k = 11 := by omega
    exact absurd hk2 (by omega)

/-- T_Λ3_02 细带案 (J=-3, m=0): k 钉死 (2k=19n+0+123−(-3)),
    k 盒 ⟹ n∈[-7,-6], 每候选角点证书 (区间角点由生成器预验·JSON 在案). -/
private lemma thin_jm3_00 (n k : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10)
    (hj : 19*n - 2*k + (0:ℤ) + 123 = (-3:ℤ))
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |((n:ℝ))*(19+a) + ((k:ℝ))*(-(2+b)) + ((0:ℤ):ℝ) + 123 - c| := by
  have hnZ : n ≤ 10 ∧ -n ≤ 10 := by omega
  have hkZ : k ≤ 10 ∧ -k ≤ 10 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  have hW1 : n ≤ -6 := by omega
  have hW2 : -7 ≤ n := by omega
  interval_cases n
  ·
    have hk2 : 2*k = -7 := by omega
    exact absurd hk2 (by omega)
  ·
    have hk2 : 2*k = 12 := by omega
    have hkv : k = 6 := by omega
    subst hkv
    set E : ℝ := (((-6:ℤ):ℝ))*(19+a) + (((6:ℤ):ℝ))*(-(2+b)) + ((0:ℤ):ℝ) + 123 - c with hE
    norm_num at hE
    ring_nf at hE
    have hside : E ≤ -(1:ℝ)/16 := by linarith
    calc (1:ℝ)/16 ≤ -(E) := by linarith
      _ ≤ |E| := neg_le_abs E

/-- T_Λ3_03 细带案 (J=-3, m=1): k 钉死 (2k=19n+1+123−(-3)),
    k 盒 ⟹ n∈[-7,-6], 每候选角点证书 (区间角点由生成器预验·JSON 在案). -/
private lemma thin_jm3_p1 (n k : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10)
    (hj : 19*n - 2*k + (1:ℤ) + 123 = (-3:ℤ))
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |((n:ℝ))*(19+a) + ((k:ℝ))*(-(2+b)) + ((1:ℤ):ℝ) + 123 - c| := by
  have hnZ : n ≤ 10 ∧ -n ≤ 10 := by omega
  have hkZ : k ≤ 10 ∧ -k ≤ 10 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  have hW1 : n ≤ -6 := by omega
  have hW2 : -7 ≤ n := by omega
  interval_cases n
  ·
    have hk2 : 2*k = -6 := by omega
    have hkv : k = -3 := by omega
    subst hkv
    set E : ℝ := (((-7:ℤ):ℝ))*(19+a) + (((-3:ℤ):ℝ))*(-(2+b)) + ((1:ℤ):ℝ) + 123 - c with hE
    norm_num at hE
    ring_nf at hE
    have hside : E ≤ -(1:ℝ)/16 := by linarith
    calc (1:ℝ)/16 ≤ -(E) := by linarith
      _ ≤ |E| := neg_le_abs E
  ·
    have hk2 : 2*k = 13 := by omega
    exact absurd hk2 (by omega)

/-- T_Λ3_04 细带案 (J=-2, m=-1): k 钉死 (2k=19n+-1+123−(-2)),
    k 盒 ⟹ n∈[-7,-6], 每候选角点证书 (区间角点由生成器预验·JSON 在案). -/
private lemma thin_jm2_m1 (n k : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10)
    (hj : 19*n - 2*k + (-1:ℤ) + 123 = (-2:ℤ))
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |((n:ℝ))*(19+a) + ((k:ℝ))*(-(2+b)) + ((-1:ℤ):ℝ) + 123 - c| := by
  have hnZ : n ≤ 10 ∧ -n ≤ 10 := by omega
  have hkZ : k ≤ 10 ∧ -k ≤ 10 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  have hW1 : n ≤ -6 := by omega
  have hW2 : -7 ≤ n := by omega
  interval_cases n
  ·
    have hk2 : 2*k = -9 := by omega
    exact absurd hk2 (by omega)
  ·
    have hk2 : 2*k = 10 := by omega
    have hkv : k = 5 := by omega
    subst hkv
    set E : ℝ := (((-6:ℤ):ℝ))*(19+a) + (((5:ℤ):ℝ))*(-(2+b)) + ((-1:ℤ):ℝ) + 123 - c with hE
    norm_num at hE
    ring_nf at hE
    have hside : E ≤ -(1:ℝ)/16 := by linarith
    calc (1:ℝ)/16 ≤ -(E) := by linarith
      _ ≤ |E| := neg_le_abs E

/-- T_Λ3_05 细带案 (J=-2, m=0): k 钉死 (2k=19n+0+123−(-2)),
    k 盒 ⟹ n∈[-7,-6], 每候选角点证书 (区间角点由生成器预验·JSON 在案). -/
private lemma thin_jm2_00 (n k : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10)
    (hj : 19*n - 2*k + (0:ℤ) + 123 = (-2:ℤ))
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |((n:ℝ))*(19+a) + ((k:ℝ))*(-(2+b)) + ((0:ℤ):ℝ) + 123 - c| := by
  have hnZ : n ≤ 10 ∧ -n ≤ 10 := by omega
  have hkZ : k ≤ 10 ∧ -k ≤ 10 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  have hW1 : n ≤ -6 := by omega
  have hW2 : -7 ≤ n := by omega
  interval_cases n
  ·
    have hk2 : 2*k = -8 := by omega
    have hkv : k = -4 := by omega
    subst hkv
    set E : ℝ := (((-7:ℤ):ℝ))*(19+a) + (((-4:ℤ):ℝ))*(-(2+b)) + ((0:ℤ):ℝ) + 123 - c with hE
    norm_num at hE
    ring_nf at hE
    have hside : E ≤ -(1:ℝ)/16 := by linarith
    calc (1:ℝ)/16 ≤ -(E) := by linarith
      _ ≤ |E| := neg_le_abs E
  ·
    have hk2 : 2*k = 11 := by omega
    exact absurd hk2 (by omega)

/-- T_Λ3_06 细带案 (J=-2, m=1): k 钉死 (2k=19n+1+123−(-2)),
    k 盒 ⟹ n∈[-7,-6], 每候选角点证书 (区间角点由生成器预验·JSON 在案). -/
private lemma thin_jm2_p1 (n k : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10)
    (hj : 19*n - 2*k + (1:ℤ) + 123 = (-2:ℤ))
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |((n:ℝ))*(19+a) + ((k:ℝ))*(-(2+b)) + ((1:ℤ):ℝ) + 123 - c| := by
  have hnZ : n ≤ 10 ∧ -n ≤ 10 := by omega
  have hkZ : k ≤ 10 ∧ -k ≤ 10 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  have hW1 : n ≤ -6 := by omega
  have hW2 : -7 ≤ n := by omega
  interval_cases n
  ·
    have hk2 : 2*k = -7 := by omega
    exact absurd hk2 (by omega)
  ·
    have hk2 : 2*k = 12 := by omega
    have hkv : k = 6 := by omega
    subst hkv
    set E : ℝ := (((-6:ℤ):ℝ))*(19+a) + (((6:ℤ):ℝ))*(-(2+b)) + ((1:ℤ):ℝ) + 123 - c with hE
    norm_num at hE
    ring_nf at hE
    have hside : E ≤ -(1:ℝ)/16 := by linarith
    calc (1:ℝ)/16 ≤ -(E) := by linarith
      _ ≤ |E| := neg_le_abs E

/-- T_Λ3_07 细带案 (J=-1, m=-1): k 钉死 (2k=19n+-1+123−(-1)),
    k 盒 ⟹ n∈[-7,-6], 每候选角点证书 (区间角点由生成器预验·JSON 在案). -/
private lemma thin_jm1_m1 (n k : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10)
    (hj : 19*n - 2*k + (-1:ℤ) + 123 = (-1:ℤ))
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |((n:ℝ))*(19+a) + ((k:ℝ))*(-(2+b)) + ((-1:ℤ):ℝ) + 123 - c| := by
  have hnZ : n ≤ 10 ∧ -n ≤ 10 := by omega
  have hkZ : k ≤ 10 ∧ -k ≤ 10 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  have hW1 : n ≤ -6 := by omega
  have hW2 : -7 ≤ n := by omega
  interval_cases n
  ·
    have hk2 : 2*k = -10 := by omega
    have hkv : k = -5 := by omega
    subst hkv
    set E : ℝ := (((-7:ℤ):ℝ))*(19+a) + (((-5:ℤ):ℝ))*(-(2+b)) + ((-1:ℤ):ℝ) + 123 - c with hE
    norm_num at hE
    ring_nf at hE
    have hside : E ≤ -(1:ℝ)/16 := by linarith
    calc (1:ℝ)/16 ≤ -(E) := by linarith
      _ ≤ |E| := neg_le_abs E
  ·
    have hk2 : 2*k = 9 := by omega
    exact absurd hk2 (by omega)

/-- T_Λ3_08 细带案 (J=-1, m=0): k 钉死 (2k=19n+0+123−(-1)),
    k 盒 ⟹ n∈[-7,-6], 每候选角点证书 (区间角点由生成器预验·JSON 在案). -/
private lemma thin_jm1_00 (n k : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10)
    (hj : 19*n - 2*k + (0:ℤ) + 123 = (-1:ℤ))
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |((n:ℝ))*(19+a) + ((k:ℝ))*(-(2+b)) + ((0:ℤ):ℝ) + 123 - c| := by
  have hnZ : n ≤ 10 ∧ -n ≤ 10 := by omega
  have hkZ : k ≤ 10 ∧ -k ≤ 10 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  have hW1 : n ≤ -6 := by omega
  have hW2 : -7 ≤ n := by omega
  interval_cases n
  ·
    have hk2 : 2*k = -9 := by omega
    exact absurd hk2 (by omega)
  ·
    have hk2 : 2*k = 10 := by omega
    have hkv : k = 5 := by omega
    subst hkv
    set E : ℝ := (((-6:ℤ):ℝ))*(19+a) + (((5:ℤ):ℝ))*(-(2+b)) + ((0:ℤ):ℝ) + 123 - c with hE
    norm_num at hE
    ring_nf at hE
    have hside : E ≤ -(1:ℝ)/16 := by linarith
    calc (1:ℝ)/16 ≤ -(E) := by linarith
      _ ≤ |E| := neg_le_abs E

/-- T_Λ3_09 细带案 (J=-1, m=1): k 钉死 (2k=19n+1+123−(-1)),
    k 盒 ⟹ n∈[-7,-6], 每候选角点证书 (区间角点由生成器预验·JSON 在案). -/
private lemma thin_jm1_p1 (n k : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10)
    (hj : 19*n - 2*k + (1:ℤ) + 123 = (-1:ℤ))
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |((n:ℝ))*(19+a) + ((k:ℝ))*(-(2+b)) + ((1:ℤ):ℝ) + 123 - c| := by
  have hnZ : n ≤ 10 ∧ -n ≤ 10 := by omega
  have hkZ : k ≤ 10 ∧ -k ≤ 10 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  have hW1 : n ≤ -6 := by omega
  have hW2 : -7 ≤ n := by omega
  interval_cases n
  ·
    have hk2 : 2*k = -8 := by omega
    have hkv : k = -4 := by omega
    subst hkv
    set E : ℝ := (((-7:ℤ):ℝ))*(19+a) + (((-4:ℤ):ℝ))*(-(2+b)) + ((1:ℤ):ℝ) + 123 - c with hE
    norm_num at hE
    ring_nf at hE
    have hside : E ≤ -(1:ℝ)/16 := by linarith
    calc (1:ℝ)/16 ≤ -(E) := by linarith
      _ ≤ |E| := neg_le_abs E
  ·
    have hk2 : 2*k = 11 := by omega
    exact absurd hk2 (by omega)

/-- T_Λ3_10 细带案 (J=0, m=-1): k 钉死 (2k=19n+-1+123−(0)),
    k 盒 ⟹ n∈[-7,-6], 每候选角点证书 (区间角点由生成器预验·JSON 在案). -/
private lemma thin_j00_m1 (n k : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10)
    (hj : 19*n - 2*k + (-1:ℤ) + 123 = (0:ℤ))
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |((n:ℝ))*(19+a) + ((k:ℝ))*(-(2+b)) + ((-1:ℤ):ℝ) + 123 - c| := by
  have hnZ : n ≤ 10 ∧ -n ≤ 10 := by omega
  have hkZ : k ≤ 10 ∧ -k ≤ 10 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  have hW1 : n ≤ -6 := by omega
  have hW2 : -7 ≤ n := by omega
  interval_cases n
  ·
    have hk2 : 2*k = -11 := by omega
    exact absurd hk2 (by omega)
  ·
    have hk2 : 2*k = 8 := by omega
    have hkv : k = 4 := by omega
    subst hkv
    set E : ℝ := (((-6:ℤ):ℝ))*(19+a) + (((4:ℤ):ℝ))*(-(2+b)) + ((-1:ℤ):ℝ) + 123 - c with hE
    norm_num at hE
    ring_nf at hE
    have hside : E ≤ -(1:ℝ)/16 := by linarith
    calc (1:ℝ)/16 ≤ -(E) := by linarith
      _ ≤ |E| := neg_le_abs E

/-- T_Λ3_11 细带案 (J=0, m=0): k 钉死 (2k=19n+0+123−(0)),
    k 盒 ⟹ n∈[-7,-6], 每候选角点证书 (区间角点由生成器预验·JSON 在案). -/
private lemma thin_j00_00 (n k : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10)
    (hj : 19*n - 2*k + (0:ℤ) + 123 = (0:ℤ))
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |((n:ℝ))*(19+a) + ((k:ℝ))*(-(2+b)) + ((0:ℤ):ℝ) + 123 - c| := by
  have hnZ : n ≤ 10 ∧ -n ≤ 10 := by omega
  have hkZ : k ≤ 10 ∧ -k ≤ 10 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  have hW1 : n ≤ -6 := by omega
  have hW2 : -7 ≤ n := by omega
  interval_cases n
  ·
    have hk2 : 2*k = -10 := by omega
    have hkv : k = -5 := by omega
    subst hkv
    set E : ℝ := (((-7:ℤ):ℝ))*(19+a) + (((-5:ℤ):ℝ))*(-(2+b)) + ((0:ℤ):ℝ) + 123 - c with hE
    norm_num at hE
    ring_nf at hE
    have hside : E ≤ -(1:ℝ)/16 := by linarith
    calc (1:ℝ)/16 ≤ -(E) := by linarith
      _ ≤ |E| := neg_le_abs E
  ·
    have hk2 : 2*k = 9 := by omega
    exact absurd hk2 (by omega)

/-- T_Λ3_12 细带案 (J=0, m=1): k 钉死 (2k=19n+1+123−(0)),
    k 盒 ⟹ n∈[-7,-6], 每候选角点证书 (区间角点由生成器预验·JSON 在案). -/
private lemma thin_j00_p1 (n k : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10)
    (hj : 19*n - 2*k + (1:ℤ) + 123 = (0:ℤ))
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |((n:ℝ))*(19+a) + ((k:ℝ))*(-(2+b)) + ((1:ℤ):ℝ) + 123 - c| := by
  have hnZ : n ≤ 10 ∧ -n ≤ 10 := by omega
  have hkZ : k ≤ 10 ∧ -k ≤ 10 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  have hW1 : n ≤ -6 := by omega
  have hW2 : -7 ≤ n := by omega
  interval_cases n
  ·
    have hk2 : 2*k = -9 := by omega
    exact absurd hk2 (by omega)
  ·
    have hk2 : 2*k = 10 := by omega
    have hkv : k = 5 := by omega
    subst hkv
    set E : ℝ := (((-6:ℤ):ℝ))*(19+a) + (((5:ℤ):ℝ))*(-(2+b)) + ((1:ℤ):ℝ) + 123 - c with hE
    norm_num at hE
    ring_nf at hE
    have hside : E ≤ -(1:ℝ)/16 := by linarith
    calc (1:ℝ)/16 ≤ -(E) := by linarith
      _ ≤ |E| := neg_le_abs E

/-- T_Λ3_13 细带案 (J=1, m=-1): k 钉死 (2k=19n+-1+123−(1)),
    k 盒 ⟹ n∈[-7,-6], 每候选角点证书 (区间角点由生成器预验·JSON 在案). -/
private lemma thin_jp1_m1 (n k : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10)
    (hj : 19*n - 2*k + (-1:ℤ) + 123 = (1:ℤ))
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |((n:ℝ))*(19+a) + ((k:ℝ))*(-(2+b)) + ((-1:ℤ):ℝ) + 123 - c| := by
  have hnZ : n ≤ 10 ∧ -n ≤ 10 := by omega
  have hkZ : k ≤ 10 ∧ -k ≤ 10 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  have hW1 : n ≤ -6 := by omega
  have hW2 : -7 ≤ n := by omega
  interval_cases n
  ·
    have hk2 : 2*k = -12 := by omega
    have hkv : k = -6 := by omega
    subst hkv
    set E : ℝ := (((-7:ℤ):ℝ))*(19+a) + (((-6:ℤ):ℝ))*(-(2+b)) + ((-1:ℤ):ℝ) + 123 - c with hE
    norm_num at hE
    ring_nf at hE
    have hside : (1:ℝ)/16 ≤ E := by linarith
    calc (1:ℝ)/16 ≤ E := hside
      _ ≤ |E| := le_abs_self E
  ·
    have hk2 : 2*k = 7 := by omega
    exact absurd hk2 (by omega)

/-- T_Λ3_14 细带案 (J=1, m=0): k 钉死 (2k=19n+0+123−(1)),
    k 盒 ⟹ n∈[-7,-6], 每候选角点证书 (区间角点由生成器预验·JSON 在案). -/
private lemma thin_jp1_00 (n k : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10)
    (hj : 19*n - 2*k + (0:ℤ) + 123 = (1:ℤ))
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |((n:ℝ))*(19+a) + ((k:ℝ))*(-(2+b)) + ((0:ℤ):ℝ) + 123 - c| := by
  have hnZ : n ≤ 10 ∧ -n ≤ 10 := by omega
  have hkZ : k ≤ 10 ∧ -k ≤ 10 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  have hW1 : n ≤ -6 := by omega
  have hW2 : -7 ≤ n := by omega
  interval_cases n
  ·
    have hk2 : 2*k = -11 := by omega
    exact absurd hk2 (by omega)
  ·
    have hk2 : 2*k = 8 := by omega
    have hkv : k = 4 := by omega
    subst hkv
    set E : ℝ := (((-6:ℤ):ℝ))*(19+a) + (((4:ℤ):ℝ))*(-(2+b)) + ((0:ℤ):ℝ) + 123 - c with hE
    norm_num at hE
    ring_nf at hE
    have hside : E ≤ -(1:ℝ)/16 := by linarith
    calc (1:ℝ)/16 ≤ -(E) := by linarith
      _ ≤ |E| := neg_le_abs E

/-- T_Λ3_15 细带案 (J=1, m=1): k 钉死 (2k=19n+1+123−(1)),
    k 盒 ⟹ n∈[-7,-6], 每候选角点证书 (区间角点由生成器预验·JSON 在案). -/
private lemma thin_jp1_p1 (n k : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10)
    (hj : 19*n - 2*k + (1:ℤ) + 123 = (1:ℤ))
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |((n:ℝ))*(19+a) + ((k:ℝ))*(-(2+b)) + ((1:ℤ):ℝ) + 123 - c| := by
  have hnZ : n ≤ 10 ∧ -n ≤ 10 := by omega
  have hkZ : k ≤ 10 ∧ -k ≤ 10 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  have hW1 : n ≤ -6 := by omega
  have hW2 : -7 ≤ n := by omega
  interval_cases n
  ·
    have hk2 : 2*k = -10 := by omega
    have hkv : k = -5 := by omega
    subst hkv
    set E : ℝ := (((-7:ℤ):ℝ))*(19+a) + (((-5:ℤ):ℝ))*(-(2+b)) + ((1:ℤ):ℝ) + 123 - c with hE
    norm_num at hE
    ring_nf at hE
    have hside : (1:ℝ)/16 ≤ E := by linarith
    calc (1:ℝ)/16 ≤ E := hside
      _ ≤ |E| := le_abs_self E
  ·
    have hk2 : 2*k = 9 := by omega
    exact absurd hk2 (by omega)

/-- T_Λ3_16 细带案 (J=2, m=-1): k 钉死 (2k=19n+-1+123−(2)),
    k 盒 ⟹ n∈[-7,-6], 每候选角点证书 (区间角点由生成器预验·JSON 在案). -/
private lemma thin_jp2_m1 (n k : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10)
    (hj : 19*n - 2*k + (-1:ℤ) + 123 = (2:ℤ))
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |((n:ℝ))*(19+a) + ((k:ℝ))*(-(2+b)) + ((-1:ℤ):ℝ) + 123 - c| := by
  have hnZ : n ≤ 10 ∧ -n ≤ 10 := by omega
  have hkZ : k ≤ 10 ∧ -k ≤ 10 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  have hW1 : n ≤ -6 := by omega
  have hW2 : -7 ≤ n := by omega
  interval_cases n
  ·
    have hk2 : 2*k = -13 := by omega
    exact absurd hk2 (by omega)
  ·
    have hk2 : 2*k = 6 := by omega
    have hkv : k = 3 := by omega
    subst hkv
    set E : ℝ := (((-6:ℤ):ℝ))*(19+a) + (((3:ℤ):ℝ))*(-(2+b)) + ((-1:ℤ):ℝ) + 123 - c with hE
    norm_num at hE
    ring_nf at hE
    have hside : (1:ℝ)/16 ≤ E := by linarith
    calc (1:ℝ)/16 ≤ E := hside
      _ ≤ |E| := le_abs_self E

/-- T_Λ3_17 细带案 (J=2, m=0): k 钉死 (2k=19n+0+123−(2)),
    k 盒 ⟹ n∈[-7,-6], 每候选角点证书 (区间角点由生成器预验·JSON 在案). -/
private lemma thin_jp2_00 (n k : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10)
    (hj : 19*n - 2*k + (0:ℤ) + 123 = (2:ℤ))
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |((n:ℝ))*(19+a) + ((k:ℝ))*(-(2+b)) + ((0:ℤ):ℝ) + 123 - c| := by
  have hnZ : n ≤ 10 ∧ -n ≤ 10 := by omega
  have hkZ : k ≤ 10 ∧ -k ≤ 10 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  have hW1 : n ≤ -6 := by omega
  have hW2 : -7 ≤ n := by omega
  interval_cases n
  ·
    have hk2 : 2*k = -12 := by omega
    have hkv : k = -6 := by omega
    subst hkv
    set E : ℝ := (((-7:ℤ):ℝ))*(19+a) + (((-6:ℤ):ℝ))*(-(2+b)) + ((0:ℤ):ℝ) + 123 - c with hE
    norm_num at hE
    ring_nf at hE
    have hside : (1:ℝ)/16 ≤ E := by linarith
    calc (1:ℝ)/16 ≤ E := hside
      _ ≤ |E| := le_abs_self E
  ·
    have hk2 : 2*k = 7 := by omega
    exact absurd hk2 (by omega)

/-- T_Λ3_18 细带案 (J=2, m=1): k 钉死 (2k=19n+1+123−(2)),
    k 盒 ⟹ n∈[-7,-6], 每候选角点证书 (区间角点由生成器预验·JSON 在案). -/
private lemma thin_jp2_p1 (n k : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10)
    (hj : 19*n - 2*k + (1:ℤ) + 123 = (2:ℤ))
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |((n:ℝ))*(19+a) + ((k:ℝ))*(-(2+b)) + ((1:ℤ):ℝ) + 123 - c| := by
  have hnZ : n ≤ 10 ∧ -n ≤ 10 := by omega
  have hkZ : k ≤ 10 ∧ -k ≤ 10 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  have hW1 : n ≤ -6 := by omega
  have hW2 : -7 ≤ n := by omega
  interval_cases n
  ·
    have hk2 : 2*k = -11 := by omega
    exact absurd hk2 (by omega)
  ·
    have hk2 : 2*k = 8 := by omega
    have hkv : k = 4 := by omega
    subst hkv
    set E : ℝ := (((-6:ℤ):ℝ))*(19+a) + (((4:ℤ):ℝ))*(-(2+b)) + ((1:ℤ):ℝ) + 123 - c with hE
    norm_num at hE
    ring_nf at hE
    have hside : (1:ℝ)/16 ≤ E := by linarith
    calc (1:ℝ)/16 ≤ E := hside
      _ ≤ |E| := le_abs_self E

/-- T_Λ3_19 细带案 (J=3, m=-1): k 钉死 (2k=19n+-1+123−(3)),
    k 盒 ⟹ n∈[-7,-6], 每候选角点证书 (区间角点由生成器预验·JSON 在案). -/
private lemma thin_jp3_m1 (n k : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10)
    (hj : 19*n - 2*k + (-1:ℤ) + 123 = (3:ℤ))
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |((n:ℝ))*(19+a) + ((k:ℝ))*(-(2+b)) + ((-1:ℤ):ℝ) + 123 - c| := by
  have hnZ : n ≤ 10 ∧ -n ≤ 10 := by omega
  have hkZ : k ≤ 10 ∧ -k ≤ 10 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  have hW1 : n ≤ -6 := by omega
  have hW2 : -7 ≤ n := by omega
  interval_cases n
  ·
    have hk2 : 2*k = -14 := by omega
    have hkv : k = -7 := by omega
    subst hkv
    set E : ℝ := (((-7:ℤ):ℝ))*(19+a) + (((-7:ℤ):ℝ))*(-(2+b)) + ((-1:ℤ):ℝ) + 123 - c with hE
    norm_num at hE
    ring_nf at hE
    have hside : (1:ℝ)/16 ≤ E := by linarith
    calc (1:ℝ)/16 ≤ E := hside
      _ ≤ |E| := le_abs_self E
  ·
    have hk2 : 2*k = 5 := by omega
    exact absurd hk2 (by omega)

/-- T_Λ3_20 细带案 (J=3, m=0): k 钉死 (2k=19n+0+123−(3)),
    k 盒 ⟹ n∈[-7,-6], 每候选角点证书 (区间角点由生成器预验·JSON 在案). -/
private lemma thin_jp3_00 (n k : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10)
    (hj : 19*n - 2*k + (0:ℤ) + 123 = (3:ℤ))
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |((n:ℝ))*(19+a) + ((k:ℝ))*(-(2+b)) + ((0:ℤ):ℝ) + 123 - c| := by
  have hnZ : n ≤ 10 ∧ -n ≤ 10 := by omega
  have hkZ : k ≤ 10 ∧ -k ≤ 10 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  have hW1 : n ≤ -6 := by omega
  have hW2 : -7 ≤ n := by omega
  interval_cases n
  ·
    have hk2 : 2*k = -13 := by omega
    exact absurd hk2 (by omega)
  ·
    have hk2 : 2*k = 6 := by omega
    have hkv : k = 3 := by omega
    subst hkv
    set E : ℝ := (((-6:ℤ):ℝ))*(19+a) + (((3:ℤ):ℝ))*(-(2+b)) + ((0:ℤ):ℝ) + 123 - c with hE
    norm_num at hE
    ring_nf at hE
    have hside : (1:ℝ)/16 ≤ E := by linarith
    calc (1:ℝ)/16 ≤ E := hside
      _ ≤ |E| := le_abs_self E

/-- T_Λ3_21 细带案 (J=3, m=1): k 钉死 (2k=19n+1+123−(3)),
    k 盒 ⟹ n∈[-7,-6], 每候选角点证书 (区间角点由生成器预验·JSON 在案). -/
private lemma thin_jp3_p1 (n k : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10)
    (hj : 19*n - 2*k + (1:ℤ) + 123 = (3:ℤ))
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |((n:ℝ))*(19+a) + ((k:ℝ))*(-(2+b)) + ((1:ℤ):ℝ) + 123 - c| := by
  have hnZ : n ≤ 10 ∧ -n ≤ 10 := by omega
  have hkZ : k ≤ 10 ∧ -k ≤ 10 := by omega
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  have hW1 : n ≤ -6 := by omega
  have hW2 : -7 ≤ n := by omega
  interval_cases n
  ·
    have hk2 : 2*k = -12 := by omega
    have hkv : k = -6 := by omega
    subst hkv
    set E : ℝ := (((-7:ℤ):ℝ))*(19+a) + (((-6:ℤ):ℝ))*(-(2+b)) + ((1:ℤ):ℝ) + 123 - c with hE
    norm_num at hE
    ring_nf at hE
    have hside : (1:ℝ)/16 ≤ E := by linarith
    calc (1:ℝ)/16 ≤ E := hside
      _ ≤ |E| := le_abs_self E
  ·
    have hk2 : 2*k = 7 := by omega
    exact absurd hk2 (by omega)

/-- T_Λ1 Λ 判定定理 (解析版主件): 证书区间内全部单项式组合与目标失配 ≥ 1/16.
    证明结构: 整数骨架 J = 19n−2k+m+123 —— |J|≥4 三角带判离 (|w|≤Wmax=2.576);
    |J|≤3 细带 21 案, 每案 k 被骨架方程钉死、k 盒把 n 压到两个候选, 角点证书判离. -/
theorem lambda_miss (n k m : ℤ) (hn : n.natAbs ≤ 10) (hk : k.natAbs ≤ 10) (hm : m.natAbs ≤ 1)
    (ha : a ∈ Icc (0.1142:ℝ) 0.1145) (hb : b ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : c ∈ Icc (0.042:ℝ) 0.061) :
    (1/16:ℝ) ≤ |(n:ℝ)*(19+a) + (k:ℝ)*(-(2+b)) + (m:ℝ) + 123 - c| := by
  have hnR := cast_abs_le n 10 hn
  have hkR := cast_abs_le k 10 hk
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  obtain ⟨J, hJdef⟩ : ∃ J : ℤ, J = 19*n - 2*k + m + 123 := ⟨_, rfl⟩
  have hD : (n:ℝ)*(19+a) + (k:ℝ)*(-(2+b)) + (m:ℝ) + 123 - c
      = (J:ℝ) + ((n:ℝ)*a - (k:ℝ)*b - c) := by
    rw [hJdef]; push_cast; ring
  by_cases hfar : (4:ℝ) ≤ |(J:ℝ)|
  · -- 三角带: |J| ≥ 4 ⟹ |D| ≥ 4 − Wmax > 1/16
    rw [hD]
    have hW1 : (n:ℝ)*a - (k:ℝ)*b - c ≤ 10*0.1145 + 10*0.1370 + 0.061 := by
      have e1 := (scale_le n a 0.1142 0.1145 hnR ⟨ha1, ha2⟩ (by norm_num)).1
      have e2 := (scale_le k b 0.1367 0.1370 hkR ⟨hb1, hb2⟩ (by norm_num)).2
      linarith
    have hW2 : -((n:ℝ)*a - (k:ℝ)*b - c) ≤ 10*0.1145 + 10*0.1370 + 0.061 := by
      have e1 := (scale_le n a 0.1142 0.1145 hnR ⟨ha1, ha2⟩ (by norm_num)).2
      have e2 := (scale_le k b 0.1367 0.1370 hkR ⟨hb1, hb2⟩ (by norm_num)).1
      linarith
    have hWabs : |(n:ℝ)*a - (k:ℝ)*b - c| ≤ 10*0.1145 + 10*0.1370 + 0.061 := by
      rw [abs_le]; constructor <;> linarith
    have htri : |(J:ℝ)| ≤ |(J:ℝ) + ((n:ℝ)*a - (k:ℝ)*b - c)|
        + |(n:ℝ)*a - (k:ℝ)*b - c| := by
      have h2 := abs_add_le ((J:ℝ) + ((n:ℝ)*a - (k:ℝ)*b - c))
        (-((n:ℝ)*a - (k:ℝ)*b - c))
      have h3 : (J:ℝ) + ((n:ℝ)*a - (k:ℝ)*b - c) + -((n:ℝ)*a - (k:ℝ)*b - c)
          = (J:ℝ) := by ring
      rw [h3, abs_neg] at h2
      exact h2
    linarith
  · -- 细带: |J| ≤ 3 ⟹ J ∈ {−3..3} × m ∈ {−1,0,1} = 21 案
    push_neg at hfar
    have h2 := abs_lt.mp hfar
    have h3 : (-4:ℤ) < J ∧ J < 4 := by exact_mod_cast h2
    have hJb1 : -3 ≤ J := by omega
    have hJb2 : J ≤ 3 := by omega
    have hm1 : -1 ≤ m := by omega
    have hm2 : m ≤ 1 := by omega
    interval_cases J

    · -- J = -3
      interval_cases m
      · exact thin_jm3_m1 a b c n k hn hk hJdef.symm ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
      · exact thin_jm3_00 a b c n k hn hk hJdef.symm ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
      · exact thin_jm3_p1 a b c n k hn hk hJdef.symm ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
    · -- J = -2
      interval_cases m
      · exact thin_jm2_m1 a b c n k hn hk hJdef.symm ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
      · exact thin_jm2_00 a b c n k hn hk hJdef.symm ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
      · exact thin_jm2_p1 a b c n k hn hk hJdef.symm ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
    · -- J = -1
      interval_cases m
      · exact thin_jm1_m1 a b c n k hn hk hJdef.symm ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
      · exact thin_jm1_00 a b c n k hn hk hJdef.symm ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
      · exact thin_jm1_p1 a b c n k hn hk hJdef.symm ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
    · -- J = 0
      interval_cases m
      · exact thin_j00_m1 a b c n k hn hk hJdef.symm ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
      · exact thin_j00_00 a b c n k hn hk hJdef.symm ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
      · exact thin_j00_p1 a b c n k hn hk hJdef.symm ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
    · -- J = 1
      interval_cases m
      · exact thin_jp1_m1 a b c n k hn hk hJdef.symm ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
      · exact thin_jp1_00 a b c n k hn hk hJdef.symm ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
      · exact thin_jp1_p1 a b c n k hn hk hJdef.symm ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
    · -- J = 2
      interval_cases m
      · exact thin_jp2_m1 a b c n k hn hk hJdef.symm ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
      · exact thin_jp2_00 a b c n k hn hk hJdef.symm ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
      · exact thin_jp2_p1 a b c n k hn hk hJdef.symm ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
    · -- J = 3
      interval_cases m
      · exact thin_jp3_m1 a b c n k hn hk hJdef.symm ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
      · exact thin_jp3_00 a b c n k hn hk hJdef.symm ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
      · exact thin_jp3_p1 a b c n k hn hk hJdef.symm ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ ⟨hc1, hc2⟩

/-- T_Λ2 纯锚推论 (log10 形式): 生成元读数与目标在证书区间内取值 ⟹
    Λ 比值目标是纯锚 (可通约谱外·N=10 盒·δ=1/16). -/
theorem lambda_pure_anchor (x α R : ℝ)
    (ha : Real.logb 10 x - 19 ∈ Icc (0.1142:ℝ) 0.1145)
    (hb : -2 - Real.logb 10 α ∈ Icc (0.1367:ℝ) 0.1370)
    (hc : Real.logb 10 R + 123 ∈ Icc (0.042:ℝ) 0.061) :
    PureAnchor (Real.logb 10 x) (Real.logb 10 α) (Real.logb 10 R) 10 (1/16:ℝ) := by
  intro n k hn hk m hm
  simp only [monoLog]
  have h := lambda_miss (a := Real.logb 10 x - 19) (b := -2 - Real.logb 10 α)
      (c := Real.logb 10 R + 123) n k m hn hk hm ha hb hc
  have h2 : (n:ℝ)*(19 + (Real.logb 10 x - 19))
      + (k:ℝ)*(-(2 + (-2 - Real.logb 10 α))) + (m:ℝ) + 123 - (Real.logb 10 R + 123)
      = (n:ℝ)*Real.logb 10 x + (k:ℝ)*Real.logb 10 α + (m:ℝ) - Real.logb 10 R := by
    ring
  rwa [h2] at h

#print axioms DualityLambda.thin_jm3_m1
#print axioms DualityLambda.thin_jm3_00
#print axioms DualityLambda.thin_jm3_p1
#print axioms DualityLambda.thin_jm2_m1
#print axioms DualityLambda.thin_jm2_00
#print axioms DualityLambda.thin_jm2_p1
#print axioms DualityLambda.thin_jm1_m1
#print axioms DualityLambda.thin_jm1_00
#print axioms DualityLambda.thin_jm1_p1
#print axioms DualityLambda.thin_j00_m1
#print axioms DualityLambda.thin_j00_00
#print axioms DualityLambda.thin_j00_p1
#print axioms DualityLambda.thin_jp1_m1
#print axioms DualityLambda.thin_jp1_00
#print axioms DualityLambda.thin_jp1_p1
#print axioms DualityLambda.thin_jp2_m1
#print axioms DualityLambda.thin_jp2_00
#print axioms DualityLambda.thin_jp2_p1
#print axioms DualityLambda.thin_jp3_m1
#print axioms DualityLambda.thin_jp3_00
#print axioms DualityLambda.thin_jp3_p1
#print axioms DualityLambda.cast_abs_le
#print axioms DualityLambda.scale_le
#print axioms DualityLambda.lambda_miss
#print axioms DualityLambda.lambda_pure_anchor
