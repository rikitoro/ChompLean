import ChompLean.PosetChomp
import Mathlib.Data.Finset.Prod

abbrev Piece := ℕ × ℕ

@[simp, grind =]
theorem Piece.le_def {p q : Piece} :
  p ≤ q ↔ p.fst ≤ q.fst ∧ p.snd ≤ q.snd := by
  rfl

@[simp, grind]
instance Piece.OrderBot : OrderBot Piece where
  bot := (0, 0)
  bot_le := by simp_all

@[simp, grind]
def Board.rectBoard (m n : ℕ) (hm : 0 < m) (hn : 0 < n): Board Piece where
  pieces := (Finset.range m).product (Finset.range n)
  hasBot := by
    simp_all [Finset.mem_product]
  downClosed := by
    intro p q hp hqp
    simp_all
    grind
