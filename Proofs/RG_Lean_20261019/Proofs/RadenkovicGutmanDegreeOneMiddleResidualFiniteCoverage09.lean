/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block000
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block001
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block002
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block003
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block004
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block005
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block006
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block007
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block008
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block009
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block010
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block011
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block012
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block013
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block014
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block015
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block016
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block017
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block018
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block019
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block020
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block021
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage09Block022
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem covered9 : decide (∀ i : Fin (RootedCatalogueData.catalogue 9).length,
    ∀ p q : Fin 5, eligible 9 i.val p.val q.val=true →
      (⟨9,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by
  rw [decide_eq_true_eq]
  intro i p q he
  have hi := i.isLt
  change i.val < 719 at hi
  by_cases h0 : i.val < 32
  · exact CoreCoverage.range_sound 9 0 32 CoreCoverage.checked9b000 i.val p q (by omega) (by omega) he
  by_cases h1 : i.val < 64
  · exact CoreCoverage.range_sound 9 32 32 CoreCoverage.checked9b001 i.val p q (by omega) (by omega) he
  by_cases h2 : i.val < 96
  · exact CoreCoverage.range_sound 9 64 32 CoreCoverage.checked9b002 i.val p q (by omega) (by omega) he
  by_cases h3 : i.val < 128
  · exact CoreCoverage.range_sound 9 96 32 CoreCoverage.checked9b003 i.val p q (by omega) (by omega) he
  by_cases h4 : i.val < 160
  · exact CoreCoverage.range_sound 9 128 32 CoreCoverage.checked9b004 i.val p q (by omega) (by omega) he
  by_cases h5 : i.val < 192
  · exact CoreCoverage.range_sound 9 160 32 CoreCoverage.checked9b005 i.val p q (by omega) (by omega) he
  by_cases h6 : i.val < 224
  · exact CoreCoverage.range_sound 9 192 32 CoreCoverage.checked9b006 i.val p q (by omega) (by omega) he
  by_cases h7 : i.val < 256
  · exact CoreCoverage.range_sound 9 224 32 CoreCoverage.checked9b007 i.val p q (by omega) (by omega) he
  by_cases h8 : i.val < 288
  · exact CoreCoverage.range_sound 9 256 32 CoreCoverage.checked9b008 i.val p q (by omega) (by omega) he
  by_cases h9 : i.val < 320
  · exact CoreCoverage.range_sound 9 288 32 CoreCoverage.checked9b009 i.val p q (by omega) (by omega) he
  by_cases h10 : i.val < 352
  · exact CoreCoverage.range_sound 9 320 32 CoreCoverage.checked9b010 i.val p q (by omega) (by omega) he
  by_cases h11 : i.val < 384
  · exact CoreCoverage.range_sound 9 352 32 CoreCoverage.checked9b011 i.val p q (by omega) (by omega) he
  by_cases h12 : i.val < 416
  · exact CoreCoverage.range_sound 9 384 32 CoreCoverage.checked9b012 i.val p q (by omega) (by omega) he
  by_cases h13 : i.val < 448
  · exact CoreCoverage.range_sound 9 416 32 CoreCoverage.checked9b013 i.val p q (by omega) (by omega) he
  by_cases h14 : i.val < 480
  · exact CoreCoverage.range_sound 9 448 32 CoreCoverage.checked9b014 i.val p q (by omega) (by omega) he
  by_cases h15 : i.val < 512
  · exact CoreCoverage.range_sound 9 480 32 CoreCoverage.checked9b015 i.val p q (by omega) (by omega) he
  by_cases h16 : i.val < 544
  · exact CoreCoverage.range_sound 9 512 32 CoreCoverage.checked9b016 i.val p q (by omega) (by omega) he
  by_cases h17 : i.val < 576
  · exact CoreCoverage.range_sound 9 544 32 CoreCoverage.checked9b017 i.val p q (by omega) (by omega) he
  by_cases h18 : i.val < 608
  · exact CoreCoverage.range_sound 9 576 32 CoreCoverage.checked9b018 i.val p q (by omega) (by omega) he
  by_cases h19 : i.val < 640
  · exact CoreCoverage.range_sound 9 608 32 CoreCoverage.checked9b019 i.val p q (by omega) (by omega) he
  by_cases h20 : i.val < 672
  · exact CoreCoverage.range_sound 9 640 32 CoreCoverage.checked9b020 i.val p q (by omega) (by omega) he
  by_cases h21 : i.val < 704
  · exact CoreCoverage.range_sound 9 672 32 CoreCoverage.checked9b021 i.val p q (by omega) (by omega) he
  exact CoreCoverage.range_sound 9 704 15 CoreCoverage.checked9b022 i.val p q (by omega) (by omega) he
#print axioms covered9
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
