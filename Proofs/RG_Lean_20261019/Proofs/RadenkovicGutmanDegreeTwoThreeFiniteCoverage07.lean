/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage07Block000
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage07Block001
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage07Block002
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage07Block003
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage07Block004
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage07Block005
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage07Block006
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage07Block007
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage07Block008
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage07Block009
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage07Block010
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage07Block011
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage07Block012
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage07Block013
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage07Block014
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem covered7 : decide (∀ i : Fin (RootedCatalogueData.catalogue 7).length,
    ∀ p q : Fin 13, eligible 7 i.val p.val q.val=true →
      (⟨7,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by
  rw [decide_eq_true_eq]
  intro i p q he
  have hi := i.isLt
  change i.val < 115 at hi
  by_cases h0 : i.val < 8
  · exact CoreCoverage.range_sound 7 0 8 CoreCoverage.checked7b000 i.val p q (by omega) (by omega) he
  ·
    by_cases h1 : i.val < 16
    · exact CoreCoverage.range_sound 7 8 8 CoreCoverage.checked7b001 i.val p q (by omega) (by omega) he
    ·
      by_cases h2 : i.val < 24
      · exact CoreCoverage.range_sound 7 16 8 CoreCoverage.checked7b002 i.val p q (by omega) (by omega) he
      ·
        by_cases h3 : i.val < 32
        · exact CoreCoverage.range_sound 7 24 8 CoreCoverage.checked7b003 i.val p q (by omega) (by omega) he
        ·
          by_cases h4 : i.val < 40
          · exact CoreCoverage.range_sound 7 32 8 CoreCoverage.checked7b004 i.val p q (by omega) (by omega) he
          ·
            by_cases h5 : i.val < 48
            · exact CoreCoverage.range_sound 7 40 8 CoreCoverage.checked7b005 i.val p q (by omega) (by omega) he
            ·
              by_cases h6 : i.val < 56
              · exact CoreCoverage.range_sound 7 48 8 CoreCoverage.checked7b006 i.val p q (by omega) (by omega) he
              ·
                by_cases h7 : i.val < 64
                · exact CoreCoverage.range_sound 7 56 8 CoreCoverage.checked7b007 i.val p q (by omega) (by omega) he
                ·
                  by_cases h8 : i.val < 72
                  · exact CoreCoverage.range_sound 7 64 8 CoreCoverage.checked7b008 i.val p q (by omega) (by omega) he
                  ·
                    by_cases h9 : i.val < 80
                    · exact CoreCoverage.range_sound 7 72 8 CoreCoverage.checked7b009 i.val p q (by omega) (by omega) he
                    ·
                      by_cases h10 : i.val < 88
                      · exact CoreCoverage.range_sound 7 80 8 CoreCoverage.checked7b010 i.val p q (by omega) (by omega) he
                      ·
                        by_cases h11 : i.val < 96
                        · exact CoreCoverage.range_sound 7 88 8 CoreCoverage.checked7b011 i.val p q (by omega) (by omega) he
                        ·
                          by_cases h12 : i.val < 104
                          · exact CoreCoverage.range_sound 7 96 8 CoreCoverage.checked7b012 i.val p q (by omega) (by omega) he
                          ·
                            by_cases h13 : i.val < 112
                            · exact CoreCoverage.range_sound 7 104 8 CoreCoverage.checked7b013 i.val p q (by omega) (by omega) he
                            ·
                              exact CoreCoverage.range_sound 7 112 3 CoreCoverage.checked7b014 i.val p q (by omega) (by omega) he
#print axioms covered7
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
