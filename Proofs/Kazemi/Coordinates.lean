module

public import Proofs.Kazemi.Geometry
public import Mathlib.Data.Fintype.Card

/-! # Coordinate equivalences preserve the actual distance-one cube graph -/

@[expose] public section
namespace Kazemi.Certificate
variable {ι κ : Type*}

def coordinateEquiv (e : ι ≃ κ) : Vertex ι ≃ Vertex κ where
  toFun x j := x (e.symm j)
  invFun y i := y (e i)
  left_inv x := by funext i; simp
  right_inv y := by funext j; simp

variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def differenceEquiv (e : ι ≃ κ) (x y : Vertex ι) :
    {i : ι // x i ≠ y i} ≃
      {j : κ // coordinateEquiv e x j ≠ coordinateEquiv e y j} where
  toFun i := ⟨e i.val, by simpa [coordinateEquiv] using i.property⟩
  invFun j := ⟨e.symm j.val, j.property⟩
  left_inv i := by apply Subtype.ext; exact e.symm_apply_apply i.val
  right_inv j := by apply Subtype.ext; exact e.apply_symm_apply j.val

theorem cube_adj_coordinateEquiv (e : ι ≃ κ) (x y : Vertex ι) :
    (cube κ).Adj (coordinateEquiv e x) (coordinateEquiv e y) ↔ (cube ι).Adj x y := by
  have hc := Fintype.card_congr (differenceEquiv e x y)
  simp only [Fintype.card_subtype] at hc
  change _ = 1 ↔ _ = 1
  rw [hc]

end Kazemi.Certificate
