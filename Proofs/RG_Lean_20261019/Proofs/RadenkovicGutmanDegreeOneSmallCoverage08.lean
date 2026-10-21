/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage08Block000
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage08Block001
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage08Block002
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage08Block003
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage08Block004
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage08Block005
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage08Block006
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage08Block007
import Proofs.RadenkovicGutmanDegreeOneSmallCoverage08Block008
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem covered8 : decide (∀ i : Fin (RootedCatalogueData.catalogue 8).length,
    ∀ p q : Fin 11, eligible 8 i.val p.val q.val=true →
      (⟨8,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by
  rw [decide_eq_true_eq]
  intro i p q he
  have hi := i.isLt
  change i.val < 286 at hi
  by_cases h0 : i.val < 32
  · exact range_sound 8 0 32 checked8b000 i.val p q (by omega) (by omega) he
  ·
    by_cases h1 : i.val < 64
    · exact range_sound 8 32 32 checked8b001 i.val p q (by omega) (by omega) he
    ·
      by_cases h2 : i.val < 96
      · exact range_sound 8 64 32 checked8b002 i.val p q (by omega) (by omega) he
      ·
        by_cases h3 : i.val < 128
        · exact range_sound 8 96 32 checked8b003 i.val p q (by omega) (by omega) he
        ·
          by_cases h4 : i.val < 160
          · exact range_sound 8 128 32 checked8b004 i.val p q (by omega) (by omega) he
          ·
            by_cases h5 : i.val < 192
            · exact range_sound 8 160 32 checked8b005 i.val p q (by omega) (by omega) he
            ·
              by_cases h6 : i.val < 224
              · exact range_sound 8 192 32 checked8b006 i.val p q (by omega) (by omega) he
              ·
                by_cases h7 : i.val < 256
                · exact range_sound 8 224 32 checked8b007 i.val p q (by omega) (by omega) he
                ·
                  exact range_sound 8 256 30 checked8b008 i.val p q (by omega) (by omega) he
#print axioms covered8
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
