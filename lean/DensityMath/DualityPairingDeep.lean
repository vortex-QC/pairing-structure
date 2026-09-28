/-
# 配对深层定理: 塌缩动力学完全分类 + 读数-塌缩互斥 + 共同确认子空间 + 同态 (T_配D/R/S/H/E, 2026-09-27)
对应: papers/对偶命题_配对深层定理_v0.1.md
体系: 对偶命题线·定理化续块 —— 定理化档 §六.4 挂账"配对深层定理"清偿
  (候令清单执行线大件②·连续谱第八块收官后对偶线仅存大件)

API 盘点 (2026-09-27·先于写码):
  - Function.iterate_succ_apply' / Function.iterate_one 在版 (Logic/Function/Iterate.lean)
  - Set.mem_range / Function.Injective 基础件在版
  - 本块承重=纯映射层 (无 Mathlib 结构依赖)——与前块自包含重述惯例同款

预注册 (先于数据·本块定理清单):
  T_配D1 轨道一步稳定: 1 ≤ n → f^[n] x = f x (幂等系统轨道至多两段)
  T_配D2 无周期轨道: f^[n] x = x (n≥1) → f x = x (确认后不再震荡·"显化定格"定理级)
  T_配R1 塌缩读数不变: r∘f∘f = r∘f (T_对1 的函数等式形式)
  T_配R2 塌缩读数必损 (本块主件): f 非恒等 → r∘f 非单射——读出吞动的读数版强化
    (T_对3 说 f 非单射·本件说 r∘f 非单射——塌缩必然损失塌缩读数的分辨力)
  T_配R3 完备读数无塌缩: r∘f 单射 → f = 恒等 (R2 逆否·D2"完备读数与塌缩互斥"纯映射层版)
  T_配S1 共同确认子空间 (本块第二主件): 幂等 f g 对易 → range(f∘g) = range f ∩ range g
    (共同确认窗=两确认窗之交——DualityPinning 共同确认子空间的纯映射层前身)
  T_配S2 共同不动点集: range(f∘g) = {x | f x = x ∧ g x = x} (对易情形)
  T_配H1 同态保不动点 / T_配H2 同态保塌缩读数 / T_配H3 复合同态 (范畴化轻量版)
  T_配E1 ℕ 塌缩族: natCollapse k (≥k 塌到 k·幂等+非恒等) + 塌缩读数必损实例 (R2 显化)
边界 (如实标): 塌缩读数必损的逆命题 (读数损 ⟹ 存在塌缩) 不在块内 (r 不变类与 f 轨道
  的完全对应需要 r 结构假设·挂账); 范畴化只到同态层 (态射+复合·未做范畴对象化);
  r 值域固定 ℕ (配对结构内置离散·与 DualityPairing 同款)。
-/
import Mathlib

namespace DualityPairingDeep

variable {X Y Z : Type*}

/-- 配对结构 (自包含重述·与 DualityPairing 同款): 确认动作 f 幂等 × 约束读出 r 离散。 -/
structure Pairing (X : Type*) where
  /-- 确认动作: 幂等自映射 -/
  f : X → X
  /-- 幂等: 读出吞动 -/
  idem : ∀ x, f (f x) = f x
  /-- 约束读出: 离散读数谱 -/
  r : X → ℕ

/-! ## T_配D 塌缩动力学 (轨道完全分类) -/

/-- T_配D1 轨道一步稳定: 幂等系统每条轨道至多两段——x ↦ f x ↦ f x ↦ …
(∀ n ≥ 1, f^[n] x = f x)。 -/
theorem orbit_stable (P : Pairing X) : ∀ (n : ℕ) (x : X), 1 ≤ n → (P.f)^[n] x = P.f x := by
  intro n
  induction n with
  | zero => intro x hn; exact absurd hn (Nat.not_succ_le_zero 0)
  | succ n ih =>
    intro x hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [Function.iterate_one]
    · rw [Function.iterate_succ_apply', ih x hpos, P.idem x]

/-- T_配D2 无周期轨道: 幂等系统无 n≥2 周期点——f^[n] x = x (n≥1) ⟹ f x = x
(确认后不再震荡·"显化定格"的定理级形态)。 -/
theorem no_periodic (P : Pairing X) (x : X) (n : ℕ) (hn : 1 ≤ n) (hper : (P.f)^[n] x = x) :
    P.f x = x := by
  rw [orbit_stable P n x hn] at hper
  exact hper

/-! ## T_配R 读数-塌缩互斥 (本块主件群) -/

/-- T_配R1 塌缩读数不变: r∘f 对确认动作不变 (r∘f∘f = r∘f)——塌缩读数
必然是确认不变的读数 (T_对1 的函数等式形式)。 -/
theorem collapse_readout_invariant (P : Pairing X) :
    (fun x => P.r (P.f (P.f x))) = (fun x => P.r (P.f x)) := by
  funext x
  rw [P.idem x]

/-- **T_配R2 塌缩读数必损 (本块主件)**: 确认动作非恒等 ⟹ 塌缩读数 r∘f 非单射——
塌缩必然损失塌缩读数的分辨力 (读出吞动的读数版强化: T_对3 说 f 非单射,
本件升到 r∘f 非单射——任何读出下塌缩都留下读数指纹重叠)。 -/
theorem collapse_loses_readout (P : Pairing X) (hne : ∃ x, P.f x ≠ x) :
    ¬ Function.Injective (fun x => P.r (P.f x)) := by
  obtain ⟨x, hx⟩ := hne
  intro hinj
  exact hx (hinj (by show P.r (P.f (P.f x)) = P.r (P.f x); rw [P.idem x]))

/-- **T_配R3 完备读数无塌缩**: 塌缩读数单射 ⟹ 确认动作恒等 (R2 逆否)——
读数完备与塌缩互斥 (D2"单投影必有损"的纯映射层强化:
读数完备的系统不需要也不会发生确认塌缩)。 -/
theorem injective_readout_no_collapse (P : Pairing X)
    (hinj : Function.Injective (fun x => P.r (P.f x))) (x : X) : P.f x = x :=
  hinj (by show P.r (P.f (P.f x)) = P.r (P.f x); rw [P.idem x])

/-! ## T_配S 共同确认子空间 (对易几何) -/

/-- **T_配S1 共同确认子空间 (本块第二主件)**: 幂等 f g 对易 ⟹
range (f∘g) = range f ∩ range g——共同确认窗恰为两确认窗之交
(DualityPinning 共同确认子空间=连线构造性存在的纯映射层前身)。 -/
theorem common_confirm_subspace {f g : X → X}
    (hf : ∀ x, f (f x) = f x) (hg : ∀ x, g (g x) = g x)
    (hcomm : ∀ x, f (g x) = g (f x)) :
    Set.range (f ∘ g) = Set.range f ∩ Set.range g := by
  ext y
  constructor
  · rintro ⟨z, hz⟩
    rw [Function.comp_apply] at hz
    have hfy : f y = y := by rw [← hz, hf (g z)]
    have hgy : g y = y := by rw [← hz, ← hcomm, hg z]
    exact ⟨Set.mem_range.mpr ⟨g z, hz⟩, Set.mem_range.mpr ⟨y, hgy⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have hfy : f y = y := by rw [← ha, hf a]
    refine Set.mem_range.mpr ⟨b, ?_⟩
    show f (g b) = y
    rw [hb, hfy]

/-- T_配S2 共同不动点集: 对易幂等的复合像=共同不动点集
(对易情形确认与读出相容的集合形态)。 -/
theorem common_fixed_eq {f g : X → X}
    (hf : ∀ x, f (f x) = f x) (hg : ∀ x, g (g x) = g x)
    (hcomm : ∀ x, f (g x) = g (f x)) :
    Set.range (f ∘ g) = {x : X | f x = x ∧ g x = x} := by
  ext y
  constructor
  · rintro ⟨z, hz⟩
    rw [Function.comp_apply] at hz
    have hfy : f y = y := by rw [← hz, hf (g z)]
    have hgy : g y = y := by rw [← hz, ← hcomm, hg z]
    exact ⟨hfy, hgy⟩
  · rintro ⟨h1, h2⟩
    refine Set.mem_range.mpr ⟨y, ?_⟩
    show f (g y) = y
    rw [h2, h1]

/-! ## T_配H 配对同态 (范畴化轻量版) -/

/-- 配对同态: 保确认动作、保读出的映射。 -/
structure PairingHom (P : Pairing X) (Q : Pairing Y) where
  /-- 底映射 -/
  toFun : X → Y
  /-- 保确认动作 -/
  hom_f : ∀ x, toFun (P.f x) = Q.f (toFun x)
  /-- 保读出 -/
  hom_r : ∀ x, Q.r (toFun x) = P.r x

/-- T_配H1 同态保不动点。 -/
theorem hom_preserves_fixed (P : Pairing X) (Q : Pairing Y) (h : PairingHom P Q)
    (x : X) (hx : P.f x = x) : Q.f (h.toFun x) = h.toFun x := by
  rw [← h.hom_f x, hx]

/-- T_配H2 同态保塌缩读数: 两侧的塌缩读数逐点对应。 -/
theorem hom_preserves_collapse_readout (P : Pairing X) (Q : Pairing Y) (h : PairingHom P Q)
    (x : X) : Q.r (Q.f (h.toFun x)) = P.r (P.f x) := by
  rw [← h.hom_f x, h.hom_r (P.f x)]

/-- T_配H3 复合同态: 配对同态对复合封闭。 -/
def hom_comp (P : Pairing X) (Q : Pairing Y) (R : Pairing Z)
    (h1 : PairingHom P Q) (h2 : PairingHom Q R) : PairingHom P R where
  toFun := h2.toFun ∘ h1.toFun
  hom_f := by
    intro x
    show h2.toFun (h1.toFun (P.f x)) = R.f (h2.toFun (h1.toFun x))
    rw [h1.hom_f x, h2.hom_f (h1.toFun x)]
  hom_r := by
    intro x
    show R.r (h2.toFun (h1.toFun x)) = P.r x
    rw [h2.hom_r (h1.toFun x), h1.hom_r x]

/-! ## T_配E 实例族 (ℕ 塌缩族) -/

/-- ℕ 塌缩族: 把 ≥ k 的自然数塌到 k (k 以下不动)——参数化塌缩配对族。 -/
def natCollapse (k : ℕ) : Pairing ℕ where
  f := fun n => if n < k then n else k
  idem := by
    intro x
    show (if (if x < k then x else k) < k then (if x < k then x else k) else k)
        = (if x < k then x else k)
    by_cases h : x < k
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg (Nat.lt_irrefl k)]
  r := fun n => n

/-- T_配E1 ℕ 塌缩族非恒等。 -/
theorem natCollapse_ne_id (k : ℕ) : ∃ n, (natCollapse k).f n ≠ n :=
  ⟨k + 1, by
    show (if k + 1 < k then k + 1 else k) ≠ k + 1
    rw [if_neg (by omega)]
    exact (Nat.lt_succ_self k).ne⟩

/-- T_配E2 ℕ 塌缩族塌缩读数必损 (主件 T_配R2 的实例化):
自然数塌缩族的塌缩读数非单射——塌缩指纹重叠的显式显化。 -/
theorem natCollapse_readout_loss (k : ℕ) :
    ¬ Function.Injective (fun n => (natCollapse k).r ((natCollapse k).f n)) :=
  collapse_loses_readout (natCollapse k) (natCollapse_ne_id k)

#print axioms DualityPairingDeep.orbit_stable
#print axioms DualityPairingDeep.no_periodic
#print axioms DualityPairingDeep.collapse_readout_invariant
#print axioms DualityPairingDeep.collapse_loses_readout
#print axioms DualityPairingDeep.injective_readout_no_collapse
#print axioms DualityPairingDeep.common_confirm_subspace
#print axioms DualityPairingDeep.common_fixed_eq
#print axioms DualityPairingDeep.hom_preserves_fixed
#print axioms DualityPairingDeep.hom_preserves_collapse_readout
#print axioms DualityPairingDeep.hom_comp
#print axioms DualityPairingDeep.natCollapse_ne_id
#print axioms DualityPairingDeep.natCollapse_readout_loss

end DualityPairingDeep
