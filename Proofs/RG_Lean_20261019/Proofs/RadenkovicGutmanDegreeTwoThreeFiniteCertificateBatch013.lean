/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0650
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0651
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0652
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0653
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0654
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0655
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0656
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0657
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0658
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0659
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0660
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0661
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0662
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0663
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0664
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0665
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0666
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0667
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0668
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0669
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0670
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0671
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0672
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0673
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0674
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0675
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0676
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0677
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0678
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0679
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0680
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0681
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0682
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0683
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0684
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0685
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0686
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0687
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0688
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0689
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0690
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0691
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0692
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0693
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0694
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0695
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0696
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0697
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0698
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0699
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys013 : ∀ k ∈ keys013, Certified k := by
  apply certified_cons (by exact certified0650)
  apply certified_cons (by exact certified0651)
  apply certified_cons (by exact certified0652)
  apply certified_cons (by exact certified0653)
  apply certified_cons (by exact certified0654)
  apply certified_cons (by exact certified0655)
  apply certified_cons (by exact certified0656)
  apply certified_cons (by exact certified0657)
  apply certified_cons (by exact certified0658)
  apply certified_cons (by exact certified0659)
  apply certified_cons (by exact certified0660)
  apply certified_cons (by exact certified0661)
  apply certified_cons (by exact certified0662)
  apply certified_cons (by exact certified0663)
  apply certified_cons (by exact certified0664)
  apply certified_cons (by exact certified0665)
  apply certified_cons (by exact certified0666)
  apply certified_cons (by exact certified0667)
  apply certified_cons (by exact certified0668)
  apply certified_cons (by exact certified0669)
  apply certified_cons (by exact certified0670)
  apply certified_cons (by exact certified0671)
  apply certified_cons (by exact certified0672)
  apply certified_cons (by exact certified0673)
  apply certified_cons (by exact certified0674)
  apply certified_cons (by exact certified0675)
  apply certified_cons (by exact certified0676)
  apply certified_cons (by exact certified0677)
  apply certified_cons (by exact certified0678)
  apply certified_cons (by exact certified0679)
  apply certified_cons (by exact certified0680)
  apply certified_cons (by exact certified0681)
  apply certified_cons (by exact certified0682)
  apply certified_cons (by exact certified0683)
  apply certified_cons (by exact certified0684)
  apply certified_cons (by exact certified0685)
  apply certified_cons (by exact certified0686)
  apply certified_cons (by exact certified0687)
  apply certified_cons (by exact certified0688)
  apply certified_cons (by exact certified0689)
  apply certified_cons (by exact certified0690)
  apply certified_cons (by exact certified0691)
  apply certified_cons (by exact certified0692)
  apply certified_cons (by exact certified0693)
  apply certified_cons (by exact certified0694)
  apply certified_cons (by exact certified0695)
  apply certified_cons (by exact certified0696)
  apply certified_cons (by exact certified0697)
  apply certified_cons (by exact certified0698)
  apply certified_cons (by exact certified0699)
  simp
#print axioms certified_keys013
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
