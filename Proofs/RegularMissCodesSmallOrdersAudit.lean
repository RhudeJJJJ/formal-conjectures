/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjectures.Paper.RegularMissCodes

example (m b : ℕ) (hm : m = 2 ∨ m = 3) (hb : b = 2 ∨ b = 3) :
    ¬ ∃ F : Finset (Finset (Fin m)), Gebendorfer.RegularMissCodes.IsMissCode m b F :=
  Gebendorfer.RegularMissCodes.small_orders m b hm hb

#print axioms Gebendorfer.RegularMissCodes.small_orders
