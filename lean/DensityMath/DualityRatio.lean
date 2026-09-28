/-
# 对偶表元约束三行结构抽象: 比值读出+约定固定点 (T_R1-T_R4, 2026-09-26)
对应: papers/对偶表_元约束三行_结构抽象_v0.1.md (c·α·Λ 三行定理级承重·结构抽象轮第一块)
体系: 对偶命题线·对偶表五行中 π/ħ 行已有 EBK 定理级 (T_EBK.2/3) —— 本块为 α/Λ 行
  (比值读出) 与 c 行 (约定固定点) 的最小形式核.

语义锚 (体系层·不进形式层——数学形态层/体系语义层分离见总标准 §五):
  - α 行: 等变读出的比值不变性 —— 耦合偏差=两力之比 (R' 型) 的读数形态;
    实测锚: Parker et al. Science 359, 191 (2018) —— α 的测量全链=无量纲频率比×质量比
    (立项档 §八⑤·一手核验毕) —— 绝对量读数缺席的实测确认.
  - Λ 行: 同一比值结构 —— Ω_Λ=ρ_Λ/ρ_c 临界密度比; 实测锚: Planck 2018/DES 2018
    全以无量纲分数报告 (立项档 §八④·一手核验毕) + P8 归约测试零命中=纯锚不可约 (纯锚带第3例).
  - c 行: 约定固定点 —— 单位重定标下读数的特征标变换+自反单位选择读数=1;
    实测锚: SI 2019 约定固定 c=299792458 m/s (精确值由定义给·非测量) ——
    元约束=单位制约定的读数锚 (尺子是观测媒介带来的·饱和端机制·描述约定层同族).
边界 (如实标): 最小假设——χ 不预设群同态 (结构一致律=深层候令);
  Λ 的纯锚不可约是数值实验级 (P8·1323 组合零命中) 不进本形式层;
  翻译层纪律: 定理级=抽象结构内, 非对物理世界的断言.
-/
import Mathlib

namespace DualityRatio

variable {G X : Type*} [Group G] [MulAction G X]

/-- 标度等变读出: 读出 φ 在标度群作用下按特征标 χ (取值实单位群·自动非零) 变换.
    最小假设: 单步等变律; χ 的群同态性 (结构一致律) 不预设——深层候令. -/
structure ScalingReadout (G X : Type*) [Group G] [MulAction G X] where
  φ : X → ℝ
  χ : G → ℝˣ
  hequiv : ∀ (g : G) (x : X), φ (g • x) = (χ g : ℝ) * φ x

/-- T_R1 比值读出不变性: 等变读出在对角作用下的比值与作用无关.
    体系语义: "偏差 (比值) 可观测、绝对量不可观测" 的算子形态
    (α=耦合偏差比值读数·Λ=临界密度比读数的共同结构核). -/
theorem ratio_invariant (E : ScalingReadout G X) (g : G) {x y : X} (hy : E.φ y ≠ 0) :
    E.φ (g • x) / E.φ (g • y) = E.φ x / E.φ y := by
  have hgy : E.φ (g • y) ≠ 0 := by
    rw [E.hequiv g y]
    exact mul_ne_zero (Units.ne_zero _) hy
  rw [E.hequiv g x, E.hequiv g y]
  field_simp

/-- T_R2 读数重定标变换律: 单位 u 重定标为 u/κ 时, 读数按 κ 特征标变换.
    体系语义: 单位制=读数框架 (描述约定层同族) —— 绝对量读数随框架变,
    比值读数不变 (T_R1 的读数框架版对偶). -/
theorem readout_rescale (q u κ : ℝ) (hκ : κ ≠ 0) (hu : u ≠ 0) :
    q / (u / κ) = κ * (q / u) := by
  field_simp

/-- T_R3 约定固定点: 把量 c 自身作约定锚生成单位 (u = c/κ₀) ⟹ 该量在
    该框架下的读数 = κ₀ 恒定 —— 精确值由约定给, 与实现无关.
    体系语义: SI 2019 的约定固定 (c=299792458 m/s) —— 元约束的约定锚定形态. -/
theorem convention_fixed (c κ₀ : ℝ) (hc : c ≠ 0) (hκ : κ₀ ≠ 0) :
    c / (c / κ₀) = κ₀ := by
  field_simp

/-- T_R4 自反读数: 取量自身为单位 ⟹ 读数 = 1 (约定固定的 κ₀=1 特例·退化锚). -/
theorem self_readout (c : ℝ) (hc : c ≠ 0) : c / c = 1 := by
  exact div_self hc

/- χ 同态性块 (结构一致律·2026-09-26 晚轻件): 最小假设块不预设 χ 同态 (挂账维持);
   本块给出 χ 升格为群同态时读出结构获得的一致性三件+钉扎点读数约束 ——
   结构一致律 = 确认动作复合下读数一致 (与 T_对5a 对易合成同族的读出面形态);
   非同态 χ ⟹ 存在点两步读数与一步读数不一致 = 读出面伪钉扎 (对应钉扎 T_P4). -/
section HomChi

/-- T_χ1 同态⟹复合读数相容: χ 群同态时, 两步作用的读出与复合作用的读出一致. -/
theorem composite_consistent (E : ScalingReadout G X)
    (hhom : ∀ a b : G, E.χ (a * b) = E.χ a * E.χ b) (g h : G) (x : X) :
    E.φ ((g * h) • x) = E.φ (g • h • x) := by
  have h1 : E.φ ((g * h) • x) = ((E.χ g : ℝ) * (E.χ h : ℝ)) * E.φ x := by
    rw [E.hequiv (g * h) x, hhom g h]
    push_cast
    ring
  have h2 : E.φ (g • h • x) = ((E.χ g : ℝ) * (E.χ h : ℝ)) * E.φ x := by
    rw [E.hequiv g (h • x), E.hequiv h x]
    ring
  rw [h1, h2]

/-- T_χ2 相容⟹同态 (非退化反向): 复合读数相容 (对一切作用与点) ⟹ χ 群同态 ——
    结构一致律的等价刻画 (特征标取值实单位群·自动非零). -/
theorem consistent_implies_hom (E : ScalingReadout G X)
    (hnondeg : ∃ x₀ : X, E.φ x₀ ≠ 0)
    (hcomp : ∀ (g h : G) (x : X), E.φ ((g * h) • x) = E.φ (g • h • x)) (a b : G) :
    E.χ (a * b) = E.χ a * E.χ b := by
  obtain ⟨x₀, hx₀⟩ := hnondeg
  have h4 : E.φ ((a * b) • x₀) = (E.χ (a * b) : ℝ) * E.φ x₀ := E.hequiv _ _
  have h3 : E.φ (a • b • x₀) = (E.χ a : ℝ) * ((E.χ b : ℝ) * E.φ x₀) := by
    rw [E.hequiv a (b • x₀), E.hequiv b x₀]
  have key : E.φ ((a * b) • x₀) = (E.χ a : ℝ) * ((E.χ b : ℝ) * E.φ x₀) := by
    rw [hcomp a b x₀]
    exact h3
  rw [h4] at key
  have hcan : (E.χ (a * b) : ℝ) * E.φ x₀
      = ((E.χ a : ℝ) * (E.χ b : ℝ)) * E.φ x₀ := by
    rw [mul_assoc]
    exact key
  exact Units.val_injective (mul_right_cancel₀ hx₀ hcan)

/-- T_χ3 钉扎点读数约束: x 为 g 的不动点 ⟹ χ(g)=1 或读数为零 ——
    被钉住的点在确认方向上无偏差 (钉扎读出面约束·可推链二的桥件). -/
theorem pinned_readout (E : ScalingReadout G X) (g : G) (x : X) (hx : g • x = x) :
    (E.χ g : ℝ) = 1 ∨ E.φ x = 0 := by
  have h : E.φ x = (E.χ g : ℝ) * E.φ x := by
    calc E.φ x = E.φ (g • x) := by rw [hx]
      _ = (E.χ g : ℝ) * E.φ x := E.hequiv g x
  have h2 : (1 - (E.χ g : ℝ)) * E.φ x = 0 := by
    rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.mp h2 with h1 | h1
  · left; linarith
  · right; exact h1

/-- T_χ4a 同态⟹单位读数 1 (χ(e)=1·正反确认互逆的前件). -/
theorem hom_one (E : ScalingReadout G X)
    (hhom : ∀ a b : G, E.χ (a * b) = E.χ a * E.χ b) :
    (E.χ (1 : G) : ℝ) = 1 := by
  have hk := hhom (1 : G) (1 : G)
  rw [mul_one] at hk
  have hk2 := hk.symm
  have h3 : (E.χ (1 : G))⁻¹ * (E.χ (1 : G) * E.χ (1 : G))
      = (E.χ (1 : G))⁻¹ * E.χ (1 : G) := by
    rw [hk2]
  have h4 : (E.χ (1 : G))⁻¹ * (E.χ (1 : G) * E.χ (1 : G)) = E.χ (1 : G) :=
    inv_mul_cancel_left _ _
  have h5 : E.χ (1 : G) = (E.χ (1 : G))⁻¹ * E.χ (1 : G) := Eq.trans h4.symm h3
  rw [inv_mul_cancel] at h5
  rw [Units.val_eq_one]
  exact h5

/-- T_χ4b 同态⟹正反确认读数互逆: χ(g⁻¹)=χ(g)⁻¹ ——
    正向确认与反向确认的读数互为倒数 (结构一致律的逆元形态). -/
theorem hom_inv (E : ScalingReadout G X)
    (hhom : ∀ a b : G, E.χ (a * b) = E.χ a * E.χ b) (g : G) :
    (E.χ (g⁻¹) : ℝ) = (E.χ g : ℝ)⁻¹ := by
  have hk := hhom g g⁻¹
  rw [mul_inv_cancel] at hk
  have h3 : ((E.χ g : ℝˣ) : ℝ) * ((E.χ (g⁻¹) : ℝˣ) : ℝ) = 1 := by
    rw [← Units.val_mul, ← hk]
    exact hom_one E hhom
  exact (inv_eq_of_mul_eq_one_right h3).symm

#print axioms DualityRatio.composite_consistent
#print axioms DualityRatio.consistent_implies_hom
#print axioms DualityRatio.pinned_readout
#print axioms DualityRatio.hom_one
#print axioms DualityRatio.hom_inv

end HomChi

end DualityRatio
