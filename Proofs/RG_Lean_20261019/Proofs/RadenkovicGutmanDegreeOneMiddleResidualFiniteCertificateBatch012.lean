/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteKeysData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0600
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0601
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0602
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0603
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0604
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0605
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0606
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0607
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0608
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0609
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0610
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0611
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0612
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0613
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0614
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0615
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0616
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0617
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0618
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0619
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0620
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0621
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0622
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0623
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0624
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0625
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0626
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0627
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0628
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0629
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0630
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0631
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0632
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0633
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0634
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0635
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0636
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0637
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0638
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0639
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0640
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0641
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0642
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0643
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0644
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0645
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0646
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0647
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0648
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0649
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneMiddleResidualFiniteActualCases
theorem certified_keys012 : ∀ k ∈ keys012, Certified k := by
  apply certified_cons (by exact certified0600)
  apply certified_cons (by exact certified0601)
  apply certified_cons (by exact certified0602)
  apply certified_cons (by exact certified0603)
  apply certified_cons (by exact certified0604)
  apply certified_cons (by exact certified0605)
  apply certified_cons (by exact certified0606)
  apply certified_cons (by exact certified0607)
  apply certified_cons (by exact certified0608)
  apply certified_cons (by exact certified0609)
  apply certified_cons (by exact certified0610)
  apply certified_cons (by exact certified0611)
  apply certified_cons (by exact certified0612)
  apply certified_cons (by exact certified0613)
  apply certified_cons (by exact certified0614)
  apply certified_cons (by exact certified0615)
  apply certified_cons (by exact certified0616)
  apply certified_cons (by exact certified0617)
  apply certified_cons (by exact certified0618)
  apply certified_cons (by exact certified0619)
  apply certified_cons (by exact certified0620)
  apply certified_cons (by exact certified0621)
  apply certified_cons (by exact certified0622)
  apply certified_cons (by exact certified0623)
  apply certified_cons (by exact certified0624)
  apply certified_cons (by exact certified0625)
  apply certified_cons (by exact certified0626)
  apply certified_cons (by exact certified0627)
  apply certified_cons (by exact certified0628)
  apply certified_cons (by exact certified0629)
  apply certified_cons (by exact certified0630)
  apply certified_cons (by exact certified0631)
  apply certified_cons (by exact certified0632)
  apply certified_cons (by exact certified0633)
  apply certified_cons (by exact certified0634)
  apply certified_cons (by exact certified0635)
  apply certified_cons (by exact certified0636)
  apply certified_cons (by exact certified0637)
  apply certified_cons (by exact certified0638)
  apply certified_cons (by exact certified0639)
  apply certified_cons (by exact certified0640)
  apply certified_cons (by exact certified0641)
  apply certified_cons (by exact certified0642)
  apply certified_cons (by exact certified0643)
  apply certified_cons (by exact certified0644)
  apply certified_cons (by exact certified0645)
  apply certified_cons (by exact certified0646)
  apply certified_cons (by exact certified0647)
  apply certified_cons (by exact certified0648)
  apply certified_cons (by exact certified0649)
  simp
#print axioms certified_keys012
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
