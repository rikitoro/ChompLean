import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod

/- # 長方形盤面の Chomp ゲームの先手必勝性に関する証明 -/

/- ## 盤面の定義 -/

/-
  m × n の初期盤面の座標は以下のように与える
poison
bot(⊥) = (0,0)   (0,1)   ⋯  (0,n-1)
          (1,0)   (1,1)   ⋯  (1,n-1)
          ⋮      ⋮           ⋮
          (m-1,0) (m-1,1) ⋯  (m-1,n-1) = top
-/

/-- Chomp の盤面のマスを表す型 -/
abbrev Piece := ℕ × ℕ

@[simp, grind]
def Piece.le (p q : Piece) : Prop :=
  p.fst ≤ q.fst ∧ p.snd ≤ q.snd

@[simp, grind]
instance Piece.LE : LE Piece where
  le := Piece.le

@[simp, grind =]
theorem Piece.le_def {p q : Piece} :
  p ≤ q ↔ p.fst ≤ q.fst ∧ p.snd ≤ q.snd := by
  rfl

/-- Chomp の毒マス (0, 0) -/
@[simp, grind]
def Piece.bot : Piece := (0, 0)

notation "⊥" => Piece.bot

@[simp, grind .]
theorem Piece.bot_le : ∀ p, ⊥ ≤ p := by
  intro p
  grind

/-- Chomp の 2 次元盤面の定義 -/
structure Board where
  pieces : Finset Piece   -- 残っているマスの集合
  hasBot : ⊥ ∈ pieces  -- 毒マス⊥が含まれている
  downClosed :          -- マス p が残っていればその左下マス q (q ≤ p)も残っている
    ∀ p q, p ∈ pieces → q ≤ p → q ∈ pieces

/-- 盤面のサイズをマスの数で定める
  NOTE : winning の定義が整礎再帰であることを示す際に使う -/
instance Board.SizeOf : SizeOf Board where
  sizeOf b := b.pieces.card

/-- 最終盤面の定義
  毒マス ⊥ のみ残っている -/
@[simp, grind]
def Board.terminal : Board where
  pieces := {⊥}
  hasBot := by grind
  downClosed := by
    intro p q hp hqp
    cases hqp with grind

@[simp, grind]
def Board.isTerminal (b : Board) : Prop :=
  b = terminal


/- ## move の定義 -/

/-- 1 手進めた盤面を返す
  残っているマス p をとったらその右下のマス q (p ≤ q) もすべて削除した盤面 b を返す(some b)
  毒マスや残っているマス以外をとった場合は失敗none -/
@[simp, grind]
def Board.move (b : Board) (p : Piece) : Option Board :=
  if h : p ∈ b.pieces ∧ p ≠ ⊥ then
    --
    let pieces := { q ∈ b.pieces | ¬ p ≤ q } -- b.Pieces.filter (fun q ↦ ¬ p ≤ q)
    --
    let botIn : ⊥ ∈ pieces := by
      simp [pieces]
      cases b with grind
    --
    let downClosed : ∀ p q, p ∈ pieces → q ≤ p → q ∈ pieces := by
      cases b with grind
    --
    some <| .mk pieces botIn downClosed
  else
    none

/-- b から b' へ合法手 1 手で進めることができる -/
@[simp, grind]
def Board.legalMove (b b' : Board) : Prop :=
  ∃ p : Piece, b.move p = some b'


/-- 一手進めると盤面のマスの数は必ず減る
  NOTE : winning の定義が整礎再帰であることを示す際に使う -/
@[simp, grind ., grind →]
theorem Board.move_size_lt {b b' : Board} (h : legalMove b b') :
  sizeOf b' < sizeOf b := by
  simp_all
  obtain ⟨p, hp⟩ := h
  apply Finset.card_lt_card
  grind

/- ## 先手必勝性の定義 -/

/-- 盤面 b に必勝手がある -/
@[simp, grind]
def Board.winning (b : Board) : Prop :=
  ∃ (b' : Board) (_ : legalMove b b'), ¬ b'.winning -- *
  decreasing_by grind
  -- NOTE : * の部分は ∃ b', legalMove b b' ∧ ¬ b'.winning と書きたいが、
  -- decreasing_by で仮定 legalMove b b' を使うため存在量化の部分に入れている。

/-- 念のため winning が望む論理式と同値であることを示しておく -/
@[simp, grind =]
theorem Board.winning_iff (b : Board) :
  b.winning ↔
  ∃ b' : Board, legalMove b b' ∧ ¬ b'.winning := by
  rw [winning]
  grind

/-- losing を winning の否定で定義 -/
@[simp, grind]
def Board.losing (b : Board) : Prop :=
  ¬ b.winning

/-- 最終盤面は負け局面である -/
@[simp, grind .]
theorem Board.terminal_losing :
  Board.terminal.losing := by
  grind


/- # 初期盤面の定義 (長方形盤面) -/

/-- m × n の長方形の盤面 -/
@[simp, grind]
def Board.rectBoard (m n : ℕ) (hm : 0 < m) (hn : 0 < n) : Board where
  pieces := (Finset.range m).product (Finset.range n)
  hasBot := by
    simp_all [Finset.mem_product]
  downClosed := by
    intro p q hp hqp
    simp_all
    grind

/-- 長方形の盤面の一番右上のピース -/
@[simp, grind]
def Piece.ttop (m n : ℕ) : Piece :=
  (m - 1, n - 1)

/-- 初期盤面では ttop ≠ ⊥ -/
@[simp, grind →, grind .]
theorem Piece.top_ne_bot {m n : ℕ} {b : Board}
  (hm : 0 < m) (hn : 0 < n)
  (h : b = Board.rectBoard m n hm hn) (hnterm : ¬ b.isTerminal) :
  ttop m n ≠ ⊥ := by
  simp_all
  grind

@[simp, grind →, grind .]
theorem Piece.le_top {m n : ℕ} {b : Board} {p : Piece}
  (hm : 0 < m) (hn : 0 < n)
  (h : b = Board.rectBoard m n hm hn) (hp : p ∈ b.pieces) :
  p ≤ ttop m n := by
  simp_all
  grind

@[simp, grind →, grind .]
theorem Piece.top_in_rectBoard {m n : ℕ} {b : Board}
  (hm : 0 < m) (hn : 0 < n)
  (h : b = Board.rectBoard m n hm hn) (hnterm : ¬ b.isTerminal) :
  ttop m n ∈ b.pieces := by
  simp_all
  grind


/- # Chomp のゲームの先手必勝性の証明 -/

/- ## 補題 -/

/-- p ≤ q ならば、「先に q で move して p で move」と
  「初めから p で move」は同じ盤面を与える -/
@[simp, grind ., grind →]
theorem Board.move_move_of_le {b b₁ b₂ : Board} {p q : Piece}
  (hqp : p ≤ q) (h₁ : b.move q = some b₁) (h₂ : b₁.move p = some b₂) :
  b.move p = some b₂ := by
  simp_all
  obtain ⟨q', hq'⟩ := h₁
  obtain ⟨p', hp'⟩ := h₂
  apply Exists.intro
  · congr
    grind
  · grind


/- ## メイン定理 -/
theorem Board.rectBoard_winning {m n b hm hn}
  (hrect : b = rectBoard m n hm hn) (hnterm : ¬ b.isTerminal) :
  b.winning := by

  -- (Aliceが) top を食べる
  let top := Piece.ttop m n
  have h_move_top : ∃ b₁, b.move top = some b₁ := by
    simp [move, top]
    grind
  obtain ⟨b₁, hb₁⟩ := h_move_top
  -- b₁ はtopが食べられた盤面
  by_cases h₁ : b₁.losing
  · grind
  · grind -- 戦略盗用が grind に隠れてしまった?!
