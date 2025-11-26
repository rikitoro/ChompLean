import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Basic

/- # 有限半順序集合での Chomp ゲームの先手必勝性に関する証明 -/

-- b.winning と b.losing b を相互再帰で定義した version


/- ## ゲーム盤面の定義 -/

variable {α : Type}
  [PartialOrder α] [OrderBot α] [DecidableEq α] [DecidableRel (α := α) (· ≤ ·)]

/-- ゲーム盤面 -/
structure Board (α : Type) -- α は各セルを表す型
  [PartialOrder α] [OrderBot α] [DecidableEq α] [DecidableRel (α := α) (· ≤ ·)]
  where
  cells : Finset α    -- 残っているセルの(有限)集合
  hasBot : ⊥ ∈ cells -- 毒セルが含まれる
  downClosed : -- 残っているセルの集合は下に閉
    ∀ p q, p ∈ cells → q ≤ p → q ∈ cells

/-- 盤面のサイズをセルの数で定義
  NOTE : winning の定義が整礎再帰であることを示す際に使う -/
@[simp, grind]
instance : SizeOf (Board α) where
  sizeOf b := b.cells.card

/-- 最終盤面(毒セルのみの負け盤面) -/
@[simp, grind]
def Board.terminal (α : Type)
  [PartialOrder α] [OrderBot α] [DecidableEq α] [DecidableRel (α := α) (· ≤ ·)]
  : Board α where
  cells := {⊥}
  hasBot := by grind
  downClosed := by
    intro p q hqp
    simp_all

@[simp, grind]
def Board.isTerminal (b : Board α) : Prop :=
  b = terminal α

/- ## move の定義 -/

/-- 盤面 b から、セル p を選んで取った盤面 b' を返す -/
@[simp, grind]
def Board.move (b : Board α) (p : α) : Option (Board α) :=
  if h : p ∈ b.cells ∧ p ≠ ⊥ then
    --
    let cells := { q ∈ b.cells | ¬ p ≤ q }
    --
    let hasBot : ⊥ ∈ cells := by
      simp [cells]
      cases b with grind
    --
    let downClosed : ∀ p q, p ∈ cells → q ≤ p → q ∈ cells := by
      cases b with grind
    --
    some <| .mk cells hasBot downClosed -- p が合法手の場合 some b'
  else
    none -- p が合法手でない場合は失敗

/-- 盤面 b から b' への合法手がある -/
@[simp, grind]
def Board.legalMove (b b' : Board α) : Prop :=
  ∃ p, b.move p = some b'

/-- 一手進めると盤面のサイズが小さくなる
  NOTE : winning の定義が整礎再帰であることを示す際に使う -/
@[simp, grind ., grind →]
theorem Board.move_size_lt {b b' : Board α} (h : legalMove b b') :
  sizeOf b' < sizeOf b := by
  simp_all
  obtain ⟨p, hp⟩ := h
  obtain ⟨hv, heq⟩ := hp
  apply Finset.card_lt_card
  simp_all [← heq, Finset.filter_ssubset]
  use p
  constructor
  · grind
  · rfl

/- ## 勝ち盤面と負け盤面の定義(相互再帰による定義) -/

mutual -- winning とlosing を相互再帰で定義

/-- 盤面 b が勝ち盤面である b.winning
  うまい一手を取ると相手に負け盤面を与えられる -/
@[grind]
def Board.winning (b : Board α) : Prop :=
  ∃ (b' : Board α) (_ : legalMove b b'), b'.losing
  decreasing_by grind

/-- 盤面 b が負け盤面である
  どんな一手をとっても相手に勝ち盤面を与える -/
@[grind]
def Board.losing (b : Board α) : Prop :=
  ∀ (b' : Board α), legalMove b b' → b'.winning
  decreasing_by grind

end

/-- 最終盤面は負け盤面 -/
@[simp, grind .]
theorem Board.terminal_losing :
  terminal α |>.losing := by
  grind

/-- 結局 losing は winning の否定 -/
@[simp, grind =]
theorem Board.losing_iff_not_winning' (b : Board α) :
  b.losing ↔ ¬ b.winning := by
  apply Iff.intro <;> intro h
  . rw [winning]
    push_neg
    intro b' hbb'
    have ih : b'.losing ↔ ¬ b'.winning := by -- 数学的帰納法
      have hlt : sizeOf b' < sizeOf b := by grind
      apply losing_iff_not_winning' b' -- 自身を再帰で呼ぶ (hlt で整礎性を示す)
    grind
  . rw [losing]
    intro b' hbb'
    have ih : b'.losing ↔ ¬ b'.winning := by -- 数学的帰納法
      have hlt : sizeOf b' < sizeOf b := by grind
      apply losing_iff_not_winning' b' -- 自身を再帰で呼ぶ (hlt で整礎性を示す)
    grind


/- ## 初期盤面の特徴付け -/

/-- 真の最大元(最小元と異なる最大元)が存在する -/
def Board.hasTtop (b : Board α) : Prop :=
  ∃ ttop ∈ b.cells, (∀ a ∈ b.cells, a ≤ ttop) ∧ ttop ≠ ⊥

/- ## 補題 -/

/-- p ≤ q のとき、q を取ってから p を取る手順は、
  はじめから p を取る手順と同じ盤面を与える (1手目はキャンセルできる) -/
@[simp, grind ., grind →]
theorem Board.move_move_of_le {b b₁ b₂ : Board α} {p q : α}
  (hqp : p ≤ q) (h₁ : b.move q = some b₁) (h₂ : b₁.move p = some b₂) :
  b.move p = some b₂ := by
  simp_all
  obtain ⟨q', hq'⟩ := h₁
  obtain ⟨p', hp'⟩ := h₂
  apply Exists.intro
  · congr
    grind
  · grind

/- ## メイン定理「真の最大元を持つ盤面は勝ち盤面」の証明 -/

theorem Board.winning_of_hasTtop {b₀ : Board α} (h : b₀.hasTtop) :
  b₀.winning := by
  obtain ⟨ttop, h₀⟩ := h -- 先手は ttop を取って move
  have h_move_ttop : ∃ b₁, b₀.move ttop = some b₁ := by
    simp_all
  obtain ⟨b₁, hb₁⟩ := h_move_ttop -- 後手は b₀ から ttop を取った盤面 b₁ を受け取る
  by_cases h₁ : b₁.losing
    <;> grind -- 戦略盗用
