/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0650
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0651
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0652
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0653
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0654
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0655
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0656
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0657
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0658
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0659
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0660
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0661
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0662
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0663
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0664
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0665
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0666
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0667
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0668
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0669
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0670
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0671
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0672
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0673
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0674
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0675
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0676
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0677
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0678
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0679
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0680
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0681
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0682
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0683
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0684
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0685
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0686
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0687
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0688
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0689
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0690
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0691
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0692
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0693
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0694
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0695
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0696
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0697
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0698
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0699
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys13 : ∀ k ∈ keys13, Certified k := by
  apply certified_cons (by exact certified0650)
  apply certified_cons (by exact certified0650swap)
  apply certified_cons (by exact certified0651)
  apply certified_cons (by exact certified0652)
  apply certified_cons (by exact certified0652swap)
  apply certified_cons (by exact certified0653)
  apply certified_cons (by exact certified0653swap)
  apply certified_cons (by exact certified0654)
  apply certified_cons (by exact certified0654swap)
  apply certified_cons (by exact certified0655)
  apply certified_cons (by exact certified0656)
  apply certified_cons (by exact certified0656swap)
  apply certified_cons (by exact certified0657)
  apply certified_cons (by exact certified0658)
  apply certified_cons (by exact certified0658swap)
  apply certified_cons (by exact certified0659)
  apply certified_cons (by exact certified0659swap)
  apply certified_cons (by exact certified0660)
  apply certified_cons (by exact certified0660swap)
  apply certified_cons (by exact certified0661)
  apply certified_cons (by exact certified0662)
  apply certified_cons (by exact certified0662swap)
  apply certified_cons (by exact certified0663)
  apply certified_cons (by exact certified0664)
  apply certified_cons (by exact certified0664swap)
  apply certified_cons (by exact certified0665)
  apply certified_cons (by exact certified0665swap)
  apply certified_cons (by exact certified0666)
  apply certified_cons (by exact certified0666swap)
  apply certified_cons (by exact certified0667)
  apply certified_cons (by exact certified0668)
  apply certified_cons (by exact certified0668swap)
  apply certified_cons (by exact certified0669)
  apply certified_cons (by exact certified0670)
  apply certified_cons (by exact certified0670swap)
  apply certified_cons (by exact certified0671)
  apply certified_cons (by exact certified0671swap)
  apply certified_cons (by exact certified0672)
  apply certified_cons (by exact certified0672swap)
  apply certified_cons (by exact certified0673)
  apply certified_cons (by exact certified0674)
  apply certified_cons (by exact certified0674swap)
  apply certified_cons (by exact certified0675)
  apply certified_cons (by exact certified0676)
  apply certified_cons (by exact certified0676swap)
  apply certified_cons (by exact certified0677)
  apply certified_cons (by exact certified0677swap)
  apply certified_cons (by exact certified0678)
  apply certified_cons (by exact certified0678swap)
  apply certified_cons (by exact certified0679)
  apply certified_cons (by exact certified0680)
  apply certified_cons (by exact certified0680swap)
  apply certified_cons (by exact certified0681)
  apply certified_cons (by exact certified0682)
  apply certified_cons (by exact certified0682swap)
  apply certified_cons (by exact certified0683)
  apply certified_cons (by exact certified0683swap)
  apply certified_cons (by exact certified0684)
  apply certified_cons (by exact certified0684swap)
  apply certified_cons (by exact certified0685)
  apply certified_cons (by exact certified0686)
  apply certified_cons (by exact certified0686swap)
  apply certified_cons (by exact certified0687)
  apply certified_cons (by exact certified0688)
  apply certified_cons (by exact certified0688swap)
  apply certified_cons (by exact certified0689)
  apply certified_cons (by exact certified0689swap)
  apply certified_cons (by exact certified0690)
  apply certified_cons (by exact certified0690swap)
  apply certified_cons (by exact certified0691)
  apply certified_cons (by exact certified0692)
  apply certified_cons (by exact certified0692swap)
  apply certified_cons (by exact certified0693)
  apply certified_cons (by exact certified0694)
  apply certified_cons (by exact certified0694swap)
  apply certified_cons (by exact certified0695)
  apply certified_cons (by exact certified0695swap)
  apply certified_cons (by exact certified0696)
  apply certified_cons (by exact certified0696swap)
  apply certified_cons (by exact certified0697)
  apply certified_cons (by exact certified0698)
  apply certified_cons (by exact certified0698swap)
  apply certified_cons (by exact certified0699)
  simp
#print axioms certified_keys13
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
