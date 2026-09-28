/-
# 对偶命题定理化: 配对核 (T_对1-T_对6, 2026-09-26)
对应: papers/对偶命题_定理化_v1.0.md (对偶命题线候令⑦·立档≠定理化缺口关闭)
体系: 对偶命题 = OMFT×D2/定理4.4×定理4.5 三线交汇推论 (C2 推论身份免检) → 公理形态+最小核

层位 (三层金字塔·假设递增):
  本件 = 配对核层: 纯映射层 —— 确认动作=幂等自映射, 约束读出=到离散型的映射.
        不假设线性/内积/完备性 —— 假设最少的抽象层.
  承重层1 = 投影假设六块 (ConfirmProj*.lean 53件): 内积空间线性层 —— 确认=P型投影.
  承重层2 = EBK定量化 (EBKQuantization.lean 10件): 谱结构层 —— 确认通道的谱离散+π/ħ分工.
  本件对象 (配对结构本身: 确认×约束读出的绑定) 在承重两层中均未单独形式化 —— 本轮补核.

语义锚 (体系层·不进形式层):
  - 确认动作 f: 显化幂等 (静的显化定义4.1) —— f∘f=f = "读出吞动"的算子形态
  - 约束读出 r: 约束是读数公式的构件 (判据B双条件: 出生L型显化∧读数结构显式位置)
  - 配对: 确认关闭所配对的自发离散特性 —— f×r 的结构绑定 (对偶命题核心)
边界 (如实标): Born权重/连续谱谱测度/bπ 不在本核 (开放挂账维持);
  π/ħ/c/α/Λ 对偶表各行中仅 π/ħ 行有定理级承重 (T_EBK.2/3) —— 其余行形式化候令.
-/
import Mathlib

namespace Duality

variable {X : Type*}

/-- 对偶配对结构: 确认动作 (幂等自映射) × 约束读出 (离散读数谱).
    r 的目标型取 ℕ (可数离散代表) —— 谱离散性在型层面内置. -/
structure Pairing (X : Type*) where
  f : X → X
  idem : f ∘ f = f
  r : X → ℕ

/-- T_对1 配对稳定性: 确认后读出不再变 —— 确认一次即定住 (读出吞动的配对形式). -/
theorem readout_stable (P : Pairing X) (x : X) :
    P.r (P.f (P.f x)) = P.r (P.f x) := by
  have h : P.f (P.f x) = P.f x := congrFun P.idem x
  rw [h]

/-- T_对2 塌缩点读出=自身读出: 不动点上确认与读出相容. -/
theorem readout_at_fixpoint (P : Pairing X) {x : X} (h : P.f x = x) :
    P.r (P.f x) = P.r x := by
  rw [h]

/-- T_对3 读出吞动 (有损的算子形态): 幂等+非恒等 ⟹ 非单射.
    确认丢弃信息 —— 塌缩不可逆的纯映射层证明. -/
theorem idempotent_not_injective (P : Pairing X) (hne : ∃ x, P.f x ≠ x) :
    ¬ Function.Injective P.f := by
  obtain ⟨x, hx⟩ := hne
  intro hinj
  exact hx (hinj (congrFun P.idem x))

/-- T_对4 确认子空间: 不动点集 = 值域 (幂等映像=不动点集).
    纯映射层的 range(M)=ker(M−I) 同构形态 —— 承重层1第三块 (ConfirmProjHilbert) 的更抽象前身. -/
theorem mem_fix_iff_mem_range (P : Pairing X) {x : X} :
    P.f x = x ↔ x ∈ Set.range P.f := by
  constructor
  · intro h; exact ⟨x, h⟩
  · intro ⟨y, hy⟩
    rw [← hy]
    exact congrFun P.idem y

section Comp
variable {f g : X → X}

/-- T_对5a 对易合成幂等: 两幂等确认动作交换 ⟹ 复合仍幂等.
    对易=比值可并存的纯映射层形态 (承重: ConfirmProjPair 线性层 T_C4.6同族). -/
theorem comp_idem_of_commute (hf : f ∘ f = f) (hg : g ∘ g = g)
    (hcomm : f ∘ g = g ∘ f) : (f ∘ g) ∘ (f ∘ g) = f ∘ g := by
  have hgf : ∀ y, g (f y) = f (g y) := fun y => (congrFun hcomm y).symm
  have hff : ∀ y, f (f y) = f y := fun y => congrFun hf y
  have hgg : ∀ y, g (g y) = g y := fun y => congrFun hg y
  funext x
  show f (g (f (g x))) = f (g x)
  rw [hgf, hgg, hff]

end Comp

/-- T_对5b 非交换反例: 两幂等确认动作不交换 ⟹ 复合语义分裂.
    Fin 3 上两个收缩映射: F 塌 1→0, G 塌 2→1; F∘G=const 0 而 G∘F(2)=1.
    单值确认互斥的纯映射层实例 (承重: ConfirmProjPair 显式 PQ≠QP 的离散版). -/
def retractionF : Fin 3 → Fin 3 := fun x => if x = 1 then 0 else x
def retractionG : Fin 3 → Fin 3 := fun x => if x = 2 then 1 else x

theorem noncommute_example :
    (retractionF ∘ retractionG) 2 ≠ (retractionG ∘ retractionF) 2 := by
  decide

/-- T_对6 非退化实例: 塌缩型配对在 Bool 上实现 —— 公理形态可满足且非退化.
    f=const true (幂等非恒等), r=指示读出; T_对3 的实例化. -/
def collapsePairing : Pairing Bool where
  f := fun _ => true
  idem := by funext x; simp [Function.comp]
  r := fun b => if b then 1 else 0

theorem collapsePairing_nondegenerate :
    (∃ x : Bool, collapsePairing.f x ≠ x) ∧
    ¬ Function.Injective collapsePairing.f := by
  constructor
  · exact ⟨false, by simp [collapsePairing]⟩
  · intro hinj
    have h : collapsePairing.f false = collapsePairing.f true := by
      simp [collapsePairing]
    exact Bool.noConfusion (hinj h)

#print axioms Duality.readout_stable
#print axioms Duality.readout_at_fixpoint
#print axioms Duality.idempotent_not_injective
#print axioms Duality.mem_fix_iff_mem_range
#print axioms Duality.comp_idem_of_commute
#print axioms Duality.noncommute_example
#print axioms Duality.collapsePairing_nondegenerate

end Duality
