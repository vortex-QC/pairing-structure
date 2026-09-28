/-
# 对偶命题应用: 观察点钉扎机理核 (T_P1-T_P5, 2026-09-26)
对应: papers/观察点钉扎层级_开放推演_v0.1.md §七 (三线推导图·可推链一的形式化)
体系: 主人两轮开放思考+定调"投影世界不动, 都立"——推导图判定"对偶命题 ⟹ 钉扎机理核"
  为可推链一, 本件把机理核从推理级升形式级 (复用配对核 DualityPairing).

层位: 配对核层之上 —— 观察点 = Pairing 的实例 (确认动作×约束读出的载体);
  双观察点 = 两个幂等确认动作 + 互读 (映射层最小假设 = 对易).

语义锚 (体系层·不进形式层):
  - 球心 = 动的观察点 (主人命题一): 等值面是读数, 读出主体位置 = 观察点;
  - 单观察点全动 = 绝对动不可自观测 (D2 动学版: 自身动无外部锚·全投影入世界) ——
    形式对应: 无第二确认动作, "共同不动子空间"概念不存在 (对照性·定义层·不单独立理);
  - 双观察点连线 = 共同确认子空间 fix f ∩ fix g —— "必然有连线"的构造性存在 (T_P2);
  - 投影世界不动 = 落在共同确认子空间的态经反复确认不变 (T_P3) —— 读出吞动的方向版;
  - 不对易互读 ⟹ 伪钉扎 (复合不动点逃出共同不动子空间·T_P4) —— 钉扎失败形态.
边界 (如实标): 互读=对易是最小映射假设 (物理实现——波动叠加/力学——不在本核);
  物理层级表 (3 点面/4 点架) 是实例化不在本核; D2 绝对量不可观测的形式件在
  Retract/DynamicLayer (单投影有损性) —— 本核不重复; 翻译层纪律: 定理级=抽象结构内.
-/
import Mathlib
import DensityMath.DualityPairing
import DensityMath.DualityRatio

namespace Duality

/-- 观察点对: 两个观察点 (各为 Pairing 实例) + 互读相容 (确认动作对易·最小映射假设). -/
structure ObservationPair (X : Type*) where
  A : Pairing X
  B : Pairing X
  commute : A.f ∘ B.f = B.f ∘ A.f

/-- T_P1 共同确认子空间 (连线的形式对应): 对易双确认下, 复合不动点
    ⟺ 双方各自不动 —— 被两个观察点共同确认的态. -/
theorem commonFix_eq (P : ObservationPair X) (x : X) :
    (P.A.f ∘ P.B.f) x = x ↔ (P.A.f x = x ∧ P.B.f x = x) := by
  have hcomm : ∀ y, P.B.f (P.A.f y) = P.A.f (P.B.f y) :=
    fun y => (congrFun P.commute y).symm
  have hA : ∀ y, P.A.f (P.A.f y) = P.A.f y := fun y => congrFun P.A.idem y
  have hB : ∀ y, P.B.f (P.B.f y) = P.B.f y := fun y => congrFun P.B.idem y
  constructor
  · intro h
    have hfg : P.A.f (P.B.f x) = x := h
    constructor
    · have h1 : P.A.f x = P.A.f (P.A.f (P.B.f x)) := by rw [hfg]
      rw [h1, hA, hfg]
    · have h2 : P.B.f x = P.B.f (P.A.f (P.B.f x)) := by rw [hfg]
      rw [h2, hcomm, hB, hfg]
  · rintro ⟨h1, h2⟩
    show P.A.f (P.B.f x) = x
    rw [h2, h1]

/-- T_P2 钉扎通道构造性存在 ("必然有连线"的形式核): 态空间非空 ⟹
    对易双确认存在共同不动点 —— 取任意态, 其复合确认即是. -/
theorem commonFix_nonempty (P : ObservationPair X) (x₀ : X) :
    ∃ x, P.A.f x = x ∧ P.B.f x = x := by
  have hcomm : ∀ y, P.B.f (P.A.f y) = P.A.f (P.B.f y) :=
    fun y => (congrFun P.commute y).symm
  have hB2 : P.B.f (P.B.f x₀) = P.B.f x₀ := congrFun P.B.idem x₀
  refine ⟨P.A.f (P.B.f x₀), ?_, ?_⟩
  · exact congrFun P.A.idem (P.B.f x₀)
  · have h1 : P.B.f (P.A.f (P.B.f x₀)) = P.A.f (P.B.f (P.B.f x₀)) := hcomm _
    rw [h1, hB2]

/-- T_P3 投影世界不动 (反复确认不变): 落在共同确认子空间的态,
    复合确认任意次不再改变 —— 读出吞动的方向版 ("都立"的分量读法形式核). -/
theorem iterate_stable (P : ObservationPair X) {x : X}
    (hA : P.A.f x = x) (hB : P.B.f x = x) (n : ℕ) :
    (P.A.f ∘ P.B.f)^[n] x = x := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    show P.A.f (P.B.f x) = x
    rw [hB, hA]

/-- T_P4 伪钉扎反例 (钉扎失败形态): 不对易互读下, 复合确认可以定住
    非共同确认的态 —— A 单方钉住的点会被 B 的确认移动.
    实例: X=Bool, A.f=const true (幂等), B.f=not (幂等); 复合=const true
    定住 true, 但 B 的确认把 true 翻成 false —— 共同不动子空间为空. -/
def pinF : Bool → Bool := fun _ => true
def pinG : Bool → Bool := not

theorem pinning_failure_example :
    (pinF ∘ pinG) true = true ∧ pinF true = true ∧ pinG true ≠ true ∧
    ¬ ∃ x : Bool, pinF x = x ∧ pinG x = x := by
  refine ⟨rfl, rfl, by decide, ?_⟩
  rintro ⟨(x | x), ⟨hF, hG⟩⟩
  · exact absurd hF (by decide : ¬(pinF false = false))
  · exact absurd hG (by decide : ¬(pinG true = true))

/-- T_P5 互读读数稳定: 共同不动点上, 一方的确认不改变另一方的读出 ——
    已钉扎的读数在互读下不被扰动 (配对稳定性 T_对1 的双点版). -/
theorem readout_mutually_stable (P : ObservationPair X) {x : X}
    (hA : P.A.f x = x) (hB : P.B.f x = x) :
    P.A.r (P.B.f x) = P.A.r x ∧ P.B.r (P.A.f x) = P.B.r x := by
  constructor
  · rw [hB]
  · rw [hA]

#print axioms Duality.commonFix_eq
#print axioms Duality.commonFix_nonempty
#print axioms Duality.iterate_stable
#print axioms Duality.pinning_failure_example
#print axioms Duality.readout_mutually_stable

section ChainTwo

variable {G X : Type*} [Group G] [MulAction G X]

/- 可推链二连接块 (钉扎 ⟹ 元约束三行读数面·2026-09-26 晚轻件):
   三线推导图 "观察点钉扎 ↓ 可推链二 (P1 全动 = 绝对量读数缺席) → 元约束三行" 的形式级连接件.
   全动 = 传递作用 (无共同不动点 = 钉扎网不完备的最小形式化) 下, 等变读出 (DualityRatio.ScalingReadout)
   的结构形态: 点身份不携带绝对读数 (T_L1) / 零点是框架事实非结构事实 (T_L2);
   钉扎侧的对应约束 = T_χ3 钉扎点读数约束 (DualityRatio.HomChi 块·不重复). -/

/-- T_L1 全动⟹绝对读数缺席: 传递作用下任意两点的读数由作用元 (特征标) 联结 ——
    读数差由群元决定而非点本身: "绝对量不可观测" (D2) 的读出面算子形态. -/
theorem absolute_absent (E : DualityRatio.ScalingReadout G X)
    (htrans : ∀ x y : X, ∃ g : G, g • x = y) (x y : X) :
    ∃ g : G, E.φ y = (E.χ g : ℝ) * E.φ x := by
  obtain ⟨g, hg⟩ := htrans x y
  exact ⟨g, by rw [← hg, E.hequiv]⟩

/-- T_L2 零点框架相对: 传递作用一点读数为零 ⟹ 处处为零 ——
    绝对读数的零点不是结构事实而是框架事实 (任何点可被作用搬到零点位置). -/
theorem zero_frame_relative (E : DualityRatio.ScalingReadout G X)
    (htrans : ∀ x y : X, ∃ g : G, g • x = y) (x₀ : X) (hx₀ : E.φ x₀ = 0) (y : X) :
    E.φ y = 0 := by
  obtain ⟨g, hg⟩ := htrans x₀ y
  rw [← hg, E.hequiv, hx₀, mul_zero]

#print axioms Duality.absolute_absent
#print axioms Duality.zero_frame_relative

end ChainTwo

end Duality
