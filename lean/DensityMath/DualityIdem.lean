/-
# 锚数 · 幂等族 (第四特例族) 登记的 Lean 承重件 (2026-09-26)
对应: papers/锚数_幂等族_第四特例族登记_v1.0.md
体系: 锚数论文 §3.4 弱约束读法 "任何提供极限的约束都可以当锚——特例层逐个立":
  势型(墙与井)/度量型(Banach 压缩)/格序型(Tarski-Knaster) 之后, 第四族=幂等族正式登记.
  主件承重 = 现有件引用 (T_对4 mem_fix_iff_mem_range / T_对5a comp_idem_of_commute /
  T_P2 commonFix_nonempty / T_N 系 netFix_iff·netFix_exists / Retract.lean 显化算子);
  本件只补族级对照件 (对齐锚数论文 "各带无锚对照" 的登记纪律).

语义锚 (体系层·不进形式层):
  - 幂等锚 = f∘f=f 的确认约束 ("读一次即定住");
  - 塌 = 每点一步塌到自己像 (局部塌) —— 对照度量族全局塌到唯一不动点;
  - 无锚对照 = 确认动作存在但无塌点 ("读而不定": 每次确认挪动态, 永不定住).
-/
import Mathlib
import DensityMath.DualityPairing

namespace Duality

section IdemFamily
variable {X : Type*}
variable {f : X → X}

/-- T_I1 一步塌定理 (幂等族核心件): 幂等确认把每个态一步塌到自己像,
    且像落在塌点集 fix f —— 塌到像集 (局部塌), 无需势/压缩速率/序结构. -/
theorem one_step_collapse (hidem : f ∘ f = f) (x : X) :
    f (f x) = f x ∧ f x ∈ Set.range f := by
  exact ⟨congrFun hidem x, ⟨x, rfl⟩⟩

/-- T_I4 非退化实例: 非恒等幂等塌缩存在 (族非空) —— Bool 常值塌缩. -/
def collapseBool : Bool → Bool := fun _ => true

theorem idem_collapse_nondegenerate :
    collapseBool ∘ collapseBool = collapseBool ∧ ∃ x : Bool, collapseBool x ≠ x := by
  refine ⟨by funext x; cases x <;> rfl, ⟨false, by simp [collapseBool]⟩⟩

end IdemFamily

/-- T_I2 族边界 (非幂等的确认动作): 后继映射"读而挪动" —— 每次确认改变态,
    不是幂等锚 (幂等性的排除面). -/
theorem succ_not_idem : ¬ (Nat.succ ∘ Nat.succ = Nat.succ) := by
  intro h
  exact absurd (congrFun h 0) (by decide)

/-- T_I3 无锚对照 (读而不定): 后继"确认"无塌点 —— 确认动作存在但 fix 为空,
    态被读着走永不定住 (对齐锚数论文三族各带无锚对照的登记纪律:
    势型对照=完备空间漂移 / 度量型对照=非压缩不收敛 / 格序型对照=非完备格无不动点;
    幂等族对照=确认动作存在但无塌点). -/
theorem succ_no_fix : ¬ ∃ x : ℕ, Nat.succ x = x := by
  rintro ⟨x, hx⟩
  omega

#print axioms Duality.one_step_collapse
#print axioms Duality.idem_collapse_nondegenerate
#print axioms Duality.succ_not_idem
#print axioms Duality.succ_no_fix

end Duality
