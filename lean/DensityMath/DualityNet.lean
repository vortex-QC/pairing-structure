/-
# 对偶命题应用: 观察点网络钉扎层级 (ObservationNet, 2026-09-26)
对应: papers/观察点钉扎层级_开放推演_v0.1.md §三 层级外推 (候令①·钉扎层级 3/4 点形式化)
体系: 承 DualityPinning (双观察点 T_P1-T_P5) —— 推广到 n 观察点网络;
  层级表 "1 点全动 → 2 点钉线 → 3 点钉面 → 4 点钉架 · 每加一个观察点显化一级静"
  (静的显化定理 3.1 的网络版) 的**序结构面**形式化:
  维数语义 (线→面→架) 是实例化层, 不在本核 (钉扎档诚实边界 6 维持).

层位: 钉扎机理核 (DualityPinning) 之上 —— 网络 = Pairing 成员的有限族 + 两两对易.

定理清单:
  T_N0  netF_nil            空网络 = 恒等 —— 0 观察点不钉任何东西 (全动基线)
  L1    netF_commute        成员与网络复合交换 ( pairwise 对易的提升)
  L2    netF_idem           网络复合幂等 (T_对5a 的族版)
  T_N1  netFix_iff          复合不动点 ⟺ 全体成员不动点 (T_P1 的 n 元推广)
  T_N2  netFix_composite / netFix_exists
                            构造性共同不动点 x* = netF fs x₀ —— "必然有共同确认子空间"
                            的 n 元版 (T_P2 推广; 连线是造出来的, 网络也是造出来的)
  T_N3  netFix_mono         加入观察点, 共同确认子空间单调不增 ——
                            "每加一个观察点显化一级静"的序结构面
  T_N4  netFix_id_observer / netFix_dup
                            恒等观察点 / 重复观察点不钉新级 ——
                            新静需要新确认维 (层级表 4 点行"无残留"的离散对应)
  T_N5  netRead_stable      钉扎态上全体互读不扰动任何读出 (T_P5 的 n 元版)
  T_N6  观察点实例 (三自由度离散链): 8 → 4 → 2 → 1 逐级钉尽
                            obsNet1_fix / obsNet2_fix / obsNet3_fix_singleton /
                            obsNet3_collapses / obsNet_chain_strict
  T_N7  第 4 观察点无新级: obsNet4_dup (重复) / obsNet4_id (恒等) / obsNet4_no_new_level
                            —— 自由度用尽后, 新观察点不显化新静

语义锚 (体系层·不进形式层):
  - netF fs = 全体观察点一次联动确认 (复合); fix(netF fs) = 共同确认子空间
    (双点"连线"的 n 元推广);
  - "1 点全动" = 单观察点自身动无外部锚 (D2 动学版) —— 对照性语义, 形式对应见
    DualityPinning 头注 (共同确认子空间概念需 ≥2 成员才产生); 本核从空网络基线
    (T_N0) 起链, 单调性 (T_N3) 给出逐级下降;
  - 三自由度实例 (T_N6/T_N7) 是层级表的**离散结构对应** (逐级严格变小 + 用尽即无新级),
    不是维数数值的对应 —— 物理 4 点钉架的刚体 6 自由度结构在实例化层;
边界 (如实标): 互读=对易是最小映射假设; 维数语义 (线/面/架) 与物理实现
  (驻波/两体约化/ICRF) 不在本核; 网络复合的顺序无关性 (任意重排同结果) 挂账.
-/
import Mathlib
import DensityMath.DualityPairing

namespace Duality

variable {X : Type*}

/-! ## 一般核: 观察点网络 -/

/-- 观察点网络: Pairing 成员的有限族 + 两两对易 (互读相容的网络化). -/
def netCommute (fs : List (Pairing X)) : Prop :=
  fs.Pairwise (fun p q => p.f ∘ q.f = q.f ∘ p.f)

/-- 网络复合确认: 全体成员一次联动确认 (foldr 复合). -/
def netF (fs : List (Pairing X)) : X → X :=
  fs.foldr (fun p acc => p.f ∘ acc) id

/-- T_N0 空网络 = 无钉扎: 没有观察点, 联动确认是恒等 —— 全动基线. -/
theorem netF_nil (x : X) : netF [] x = x := rfl

/-- L1 成员与网络复合交换: p 与 fs 中全部成员对易 ⟹ p.f 穿过整个网络复合.
    对易逐个提升到复合的归纳. -/
theorem netF_commute (p : Pairing X) (z : X) : ∀ fs : List (Pairing X),
    (∀ q ∈ fs, p.f ∘ q.f = q.f ∘ p.f) → p.f (netF fs z) = netF fs (p.f z) := by
  intro fs
  induction fs with
  | nil => intro _; rfl
  | cons q rest ih =>
    intro hp
    have hqp : ∀ y, p.f (q.f y) = q.f (p.f y) :=
      fun y => congrFun (hp q List.mem_cons_self) y
    have hih : p.f (netF rest z) = netF rest (p.f z) :=
      ih (fun q' hq' => hp q' (List.mem_cons_of_mem q hq'))
    show p.f (q.f (netF rest z)) = q.f (netF rest (p.f z))
    rw [hqp, hih]

/-- L2 网络复合幂等: 两两对易的幂等确认族, 其联动复合仍幂等 (T_对5a 的族版). -/
theorem netF_idem (z : X) : ∀ fs : List (Pairing X), netCommute fs →
    netF fs (netF fs z) = netF fs z := by
  intro fs
  induction fs with
  | nil => intro _; rfl
  | cons q rest ih =>
    intro hc
    obtain ⟨hmem, hrest⟩ := List.pairwise_cons.mp hc
    show q.f (netF rest (q.f (netF rest z))) = q.f (netF rest z)
    rw [(netF_commute q (netF rest z) rest hmem).symm, ih hrest]
    exact congrFun q.idem (netF rest z)

/-- T_N1 复合不动点 ⟺ 全体成员不动点 (→ 方向): 被网络联动确认一次定住的态,
    被每个观察点各自确认也定住 —— 钉住 = 同时被全体确认 (T_P1 的 n 元推广). -/
theorem netFix_forall_of_fix (x : X) : ∀ fs : List (Pairing X), netCommute fs →
    netF fs x = x → ∀ p ∈ fs, p.f x = x := by
  intro fs
  induction fs with
  | nil => intro _ _ p hp; cases hp
  | cons q rest ih =>
    intro hc hx p hp
    obtain ⟨hmem, hrest⟩ := List.pairwise_cons.mp hc
    have hx' : q.f (netF rest x) = x := hx
    have h1 : netF rest x = x := by
      calc netF rest x
          = netF rest (q.f (netF rest x)) := by rw [hx']
        _ = q.f (netF rest (netF rest x)) := (netF_commute q (netF rest x) rest hmem).symm
        _ = q.f (netF rest x) := by rw [netF_idem x rest hrest]
        _ = x := hx'
    rcases List.mem_cons.mp hp with hpq | hp'
    · rw [hpq]
      have hq2 : q.f x = q.f (netF rest x) := by rw [h1]
      rw [hq2]
      exact hx
    · exact ih hrest h1 p hp'

/-- T_N1 (← 方向): 全体成员各自确认 ⟹ 联动复合确认 (无需对易——逐个应用即得). -/
theorem netFix_of_forall (x : X) : ∀ fs : List (Pairing X),
    (∀ p ∈ fs, p.f x = x) → netF fs x = x := by
  intro fs
  induction fs with
  | nil => intro _; rfl
  | cons q rest ih =>
    intro hp
    show q.f (netF rest x) = x
    rw [ih fun p hmem => hp p (List.mem_cons_of_mem q hmem)]
    exact hp q List.mem_cons_self

/-- T_N1 合取: 对易网络下, 联动确认的钉住 ⟺ 全体观察点的共同确认
    (共同确认子空间 = fix(netF fs), 双点"连线" T_P1 的 n 元推广). -/
theorem netFix_iff (fs : List (Pairing X)) (hc : netCommute fs) (x : X) :
    netF fs x = x ↔ ∀ p ∈ fs, p.f x = x :=
  ⟨netFix_forall_of_fix x fs hc, netFix_of_forall x fs⟩

/-- T_N2' 构造性钉扎 (逐点版): 对易网络的联动复合 netF fs x₀ 被每个成员确认定住
    —— 把任意态喂进网络, 出来的就是共同确认态 ("共同确认子空间是造出来的"). -/
theorem netFix_composite (x₀ : X) : ∀ fs : List (Pairing X), netCommute fs →
    ∀ p ∈ fs, p.f (netF fs x₀) = netF fs x₀ := by
  intro fs
  induction fs with
  | nil => intro _ p hp; cases hp
  | cons q rest ih =>
    intro hc p hp
    obtain ⟨hmem, hrest⟩ := List.pairwise_cons.mp hc
    rcases List.mem_cons.mp hp with hpq | hp'
    · rw [hpq]
      show q.f (q.f (netF rest x₀)) = q.f (netF rest x₀)
      exact congrFun q.idem (netF rest x₀)
    · show p.f (q.f (netF rest x₀)) = q.f (netF rest x₀)
      have hcomm : ∀ y, p.f (q.f y) = q.f (p.f y) :=
        fun y => congrFun (hmem p hp').symm y
      rw [hcomm, ih hrest p hp']

/-- T_N2 构造性共同不动点 (存在版, T_P2 的 n 元推广): 态空间非空 ⟹
    对易网络存在共同确认态 —— "必然有共同确认子空间"的网络版. -/
theorem netFix_exists (fs : List (Pairing X)) (hc : netCommute fs) (x₀ : X) :
    ∃ x, netF fs x = x ∧ ∀ p ∈ fs, p.f x = x :=
  ⟨netF fs x₀, netF_idem x₀ fs hc, fun p hp => netFix_composite x₀ fs hc p hp⟩

/-- T_N3 单调不增 (每加一个观察点显化一级·序结构面): 对易网络加入新观察点,
    共同确认子空间只缩小或不变 —— 静的单调显化. -/
theorem netFix_mono (p : Pairing X) (fs : List (Pairing X))
    (hc : netCommute (p :: fs)) (x : X) (hx : netF (p :: fs) x = x) :
    netF fs x = x := by
  obtain ⟨_, hrest⟩ := List.pairwise_cons.mp hc
  exact (netFix_iff fs hrest x).mpr
    (fun q hq => (netFix_iff (p :: fs) hc x).1 hx q (List.mem_cons_of_mem p hq))

/-- T_N4a 恒等观察点不钉新级: 确认动作为恒等的观察点 (读了但没锁) 不改变
    共同确认子空间 —— 新静需要新确认维 (无需对易, 恒等穿过任何复合). -/
theorem netFix_id_observer (p : Pairing X) (fs : List (Pairing X))
    (hid : p.f = id) (x : X) :
    (netF (p :: fs) x = x ↔ netF fs x = x) := by
  show p.f (netF fs x) = x ↔ netF fs x = x
  rw [hid]
  simp

/-- T_N4b 重复观察点不钉新级: 同一确认动作出现两次, 联动复合不变
    (幂等自吸收; 无需对易). -/
theorem netFix_dup (p : Pairing X) (fs : List (Pairing X)) (x : X) :
    netF (p :: p :: fs) x = netF (p :: fs) x := by
  show p.f (p.f (netF fs x)) = p.f (netF fs x)
  exact congrFun p.idem (netF fs x)

/-- T_N5 互读读出稳定 n 元版: 钉扎态上, 任何成员的确认不改变任何成员的读出
    (T_P5 的网络版 —— 已钉扎的读数在全网互读下不被扰动). -/
theorem netRead_stable (fs : List (Pairing X)) (hc : netCommute fs) (x : X)
    (hx : netF fs x = x) : ∀ p ∈ fs, ∀ q ∈ fs, p.r (q.f x) = p.r x := by
  intro p hp q hq
  rw [(netFix_iff fs hc x).1 hx q hq]

/-! ## 显式实例: 三自由度离散链 (层级表的离散结构对应) -/

/-- 三自由度离散态空间: (Fin 2)³, 8 态, 每个分量 = 一个待钉自由度. -/
abbrev Obs3 := Fin 2 × Fin 2 × Fin 2

/-- 观察点 1: 确认动作 = 塌缩第一分量 (读出 = 第一分量). -/
def obsF1 : Obs3 → Obs3 := fun p => (0, p.2.1, p.2.2)

/-- 观察点 2: 确认动作 = 塌缩第二分量. -/
def obsF2 : Obs3 → Obs3 := fun p => (p.1, 0, p.2.2)

/-- 观察点 3: 确认动作 = 塌缩第三分量. -/
def obsF3 : Obs3 → Obs3 := fun p => (p.1, p.2.1, 0)

theorem obsF1_idem : obsF1 ∘ obsF1 = obsF1 := by
  funext x; rcases x with ⟨a, b, c⟩; simp [obsF1]

theorem obsF2_idem : obsF2 ∘ obsF2 = obsF2 := by
  funext x; rcases x with ⟨a, b, c⟩; simp [obsF2]

theorem obsF3_idem : obsF3 ∘ obsF3 = obsF3 := by
  funext x; rcases x with ⟨a, b, c⟩; simp [obsF3]

theorem obsF1_obsF2_commute : obsF1 ∘ obsF2 = obsF2 ∘ obsF1 := by
  funext x; rcases x with ⟨a, b, c⟩; simp [obsF1, obsF2]

theorem obsF1_obsF3_commute : obsF1 ∘ obsF3 = obsF3 ∘ obsF1 := by
  funext x; rcases x with ⟨a, b, c⟩; simp [obsF1, obsF3]

theorem obsF2_obsF3_commute : obsF2 ∘ obsF3 = obsF3 ∘ obsF2 := by
  funext x; rcases x with ⟨a, b, c⟩; simp [obsF2, obsF3]

/-- 三个观察点 (各塌缩一个分量, 各带自己的读出). -/
def obsP1 : Pairing Obs3 := ⟨obsF1, obsF1_idem, fun p => p.1.val⟩
def obsP2 : Pairing Obs3 := ⟨obsF2, obsF2_idem, fun p => p.2.1.val⟩
def obsP3 : Pairing Obs3 := ⟨obsF3, obsF3_idem, fun p => p.2.2.val⟩

/-- 三观察点网络. -/
def obsNet3 : List (Pairing Obs3) := [obsP1, obsP2, obsP3]

theorem obsNet3_commute : netCommute obsNet3 := by
  unfold netCommute obsNet3
  refine List.pairwise_cons.mpr ⟨?_,
    List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, List.Pairwise.nil⟩⟩⟩
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact obsF1_obsF2_commute
    · rcases List.mem_singleton.mp hq' with rfl
      exact obsF1_obsF3_commute
  · intro q hq
    rcases List.mem_singleton.mp hq with rfl
    exact obsF2_obsF3_commute
  · intro q hq
    cases hq

/-- T_N6c 三点钉尽: 三观察点联动确认把任何态塌到原点 (全部自由度钉完). -/
theorem obsNet3_collapses (x : Obs3) : netF obsNet3 x = (0, 0, 0) := by
  show obsF1 (obsF2 (obsF3 x)) = (0, 0, 0)
  rcases x with ⟨a, b, c⟩
  simp [obsF1, obsF2, obsF3]

/-- T_N6c 钉尽定理: 三观察点网络的共同确认子空间 = 单点 (离散版"架完成"). -/
theorem obsNet3_fix_singleton (x : Obs3) :
    netF obsNet3 x = x ↔ x = (0, 0, 0) := by
  rw [obsNet3_collapses]
  exact eq_comm

/-- T_N6a 一点钉一级: 单观察点的确认子空间 = 第一分量归零 (8 态剩 4 态). -/
theorem obsNet1_fix (x : Obs3) : netF [obsP1] x = x ↔ x.1 = 0 := by
  rcases x with ⟨a, b, c⟩
  fin_cases a <;> simp [netF, obsP1, obsF1]

/-- T_N6b 两点钉两级: 双观察点确认子空间 = 前两分量归零 (8 态剩 2 态). -/
theorem obsNet2_fix (x : Obs3) :
    netF [obsP1, obsP2] x = x ↔ x.1 = 0 ∧ x.2.1 = 0 := by
  rcases x with ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> simp [netF, obsP1, obsP2, obsF1, obsF2]

/-- 链的严格性见证: (0,1,0) 被一点钉住但被两点挪走 —— 每级严格变小
    ("每加一个观察点显化一级静"的显式实例, T_N3 单调性的严格侧). -/
theorem obsNet_chain_strict :
    netF [obsP1] (0, 1, 0) = (0, 1, 0) ∧ netF [obsP1, obsP2] (0, 1, 0) ≠ (0, 1, 0) := by
  constructor
  · simp [netF, obsP1, obsF1]
  · simp [netF, obsP1, obsP2, obsF1, obsF2]

/-- 第 4 观察点 (重复型): 与观察点 1 相同的确认动作. -/
def obsP4dup : Pairing Obs3 := ⟨obsF1, obsF1_idem, fun p => p.1.val⟩

/-- 第 4 观察点 (恒等型): 读了但没锁 (确认动作 = 恒等). -/
def obsP4id : Pairing Obs3 := ⟨id, rfl, fun _ => 0⟩

/-- T_N7 重复型第 4 观察点无新级: 联动复合逐点不变 (幂等自吸收). -/
theorem obsNet4_dup (x : Obs3) : netF (obsP4dup :: obsNet3) x = netF obsNet3 x := by
  show obsF1 (netF obsNet3 x) = netF obsNet3 x
  rw [obsNet3_collapses]
  simp [obsF1]

/-- T_N7 恒等型第 4 观察点无新级: 联动复合逐点不变 (恒等穿过). -/
theorem obsNet4_id (x : Obs3) : netF (obsP4id :: obsNet3) x = netF obsNet3 x := by
  show id (netF obsNet3 x) = netF obsNet3 x
  rfl

/-- T_N7 合取: 自由度用尽后, 第 4 观察点 (无论重复还是恒等) 不显化新静 ——
    层级表 4 点行"不可读残留 = 无"的离散结构对应. -/
theorem obsNet4_no_new_level (x : Obs3) :
    (netF (obsP4dup :: obsNet3) x = x ↔ netF obsNet3 x = x) ∧
    (netF (obsP4id :: obsNet3) x = x ↔ netF obsNet3 x = x) := by
  constructor
  · constructor
    · intro h; rw [obsNet4_dup x] at h; exact h
    · intro h; rw [obsNet4_dup x]; exact h
  · constructor
    · intro h; rw [obsNet4_id x] at h; exact h
    · intro h; rw [obsNet4_id x]; exact h

/-! ## 顺序无关性（候令②·快件）: 网络复合与排列/拼接顺序 -/

/-- 块折叠引理（无对易需求）: 网络复合按拼接分块 —— 先 gs 后 fs.
    归纳直接证. -/
theorem netF_append (fs gs : List (Pairing X)) (x : X) :
    netF (fs ++ gs) x = netF fs (netF gs x) := by
  induction fs with
  | nil => rfl
  | cons q rest ih =>
    show q.f (netF (rest ++ gs) x) = q.f (netF rest (netF gs x))
    rw [ih]

/-- 块与块对易（L1 的块版）: fs 与 gs 全员互对易 ⟹ 网络复合块可交换.
    头部成员经 L1 穿过整块 gs + 尾部块经归纳 —— 两次提升. -/
theorem netF_block_commute (fs : List (Pairing X)) :
    ∀ gs : List (Pairing X), (∀ p ∈ fs, ∀ q ∈ gs, p.f ∘ q.f = q.f ∘ p.f) →
      netF fs ∘ netF gs = netF gs ∘ netF fs := by
  intro gs
  induction fs with
  | nil => intro _; simp [netF]
  | cons q rest ih =>
    intro hall
    have hq : ∀ y, q.f (netF gs y) = netF gs (q.f y) :=
      fun y => netF_commute q y gs
        (fun q' hq' => hall q List.mem_cons_self q' hq')
    have hrest : ∀ y, netF rest (netF gs y) = netF gs (netF rest y) :=
      fun y => congrFun (ih fun p hp q' hq' => hall p (List.mem_cons_of_mem q hp) q' hq') y
    funext x
    show q.f (netF rest (netF gs x)) = netF gs (q.f (netF rest x))
    rw [hrest x, hq]

/-- T_N8 拼接顺序无关: 两块观察点全员互对易时, 网络复合与拼接顺序无关
    （观察点集合无序的 append 形态）. -/
theorem netF_append_comm (fs gs : List (Pairing X))
    (hall : ∀ p ∈ fs, ∀ q ∈ gs, p.f ∘ q.f = q.f ∘ p.f) (x : X) :
    netF (fs ++ gs) x = netF (gs ++ fs) x := by
  rw [netF_append, netF_append]
  exact congrFun (netF_block_commute fs gs hall) x

/-- T_N9 顺序无关主件（Perm 形态）: 两两对易是排列不变的, 且网络复合在排列下
    逐点不变 —— 对易性结论与函数等式一起给出（不依赖 Pairwise 的 Perm 稳定引理）. -/
theorem netF_perm (fs₁ fs₂ : List (Pairing X)) (hp : fs₁.Perm fs₂) :
    netCommute fs₁ → netCommute fs₂ ∧ netF fs₁ = netF fs₂ := by
  induction hp with
  | nil => intro hc; exact ⟨hc, rfl⟩
  | @cons x l₁ l₂ h ih =>
    intro hc
    obtain ⟨hmem, hrest⟩ := List.pairwise_cons.mp hc
    obtain ⟨hc₂, hf₂⟩ := ih hrest
    refine ⟨List.pairwise_cons.mpr ⟨fun q hq => hmem q ?_, hc₂⟩, ?_⟩
    · exact (List.Perm.mem_iff (a := q) h).symm.mp hq
    · funext x'
      show x.f (netF l₁ x') = x.f (netF l₂ x')
      rw [hf₂]
  | swap a b l =>
    intro hc
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hc
    obtain ⟨hatail, hl⟩ := List.pairwise_cons.mp htail
    have hab : a.f ∘ b.f = b.f ∘ a.f := (hhead a List.mem_cons_self).symm
    refine ⟨List.pairwise_cons.mpr ⟨fun c hcb => ?_,
      List.pairwise_cons.mpr ⟨fun c hcl => hhead c (List.mem_cons_of_mem _ hcl), hl⟩⟩, ?_⟩
    · rcases List.mem_cons.mp hcb with rfl | hcl
      · exact hab
      · exact hatail c hcl
    · funext x
      show b.f (a.f (netF l x)) = a.f (b.f (netF l x))
      exact (congrFun hab (netF l x)).symm
  | trans _ _ ih₁ ih₂ =>
    intro hc
    obtain ⟨hc₂, hf₁⟩ := ih₁ hc
    obtain ⟨hc₃, hf₂⟩ := ih₂ hc₂
    exact ⟨hc₃, hf₁.trans hf₂⟩

/-- T_N9 实例: 三观察点网络重排不变 —— 交换 obsP1/obsP2 顺序, 联动复合逐点不变. -/
theorem obsNet3_swap (x : Obs3) :
    netF [obsP2, obsP1, obsP3] x = netF obsNet3 x := by
  have hp : obsNet3.Perm [obsP2, obsP1, obsP3] :=
    (List.Perm.swap obsP1 obsP2 [obsP3]).symm
  exact congrFun (netF_perm _ _ hp obsNet3_commute).2.symm x

#print axioms Duality.netF_nil
#print axioms Duality.netF_commute
#print axioms Duality.netF_idem
#print axioms Duality.netFix_forall_of_fix
#print axioms Duality.netFix_of_forall
#print axioms Duality.netFix_iff
#print axioms Duality.netFix_composite
#print axioms Duality.netFix_exists
#print axioms Duality.netFix_mono
#print axioms Duality.netFix_id_observer
#print axioms Duality.netFix_dup
#print axioms Duality.netRead_stable
#print axioms Duality.obsNet3_collapses
#print axioms Duality.obsNet3_fix_singleton
#print axioms Duality.obsNet1_fix
#print axioms Duality.obsNet2_fix
#print axioms Duality.obsNet_chain_strict
#print axioms Duality.obsNet4_dup
#print axioms Duality.obsNet4_id
#print axioms Duality.obsNet4_no_new_level
#print axioms Duality.netF_append
#print axioms Duality.netF_block_commute
#print axioms Duality.netF_append_comm
#print axioms Duality.netF_perm
#print axioms Duality.obsNet3_swap

end Duality
