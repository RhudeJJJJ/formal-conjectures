/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0600
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0601
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0602
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0603
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0604
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0605
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0606
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0607
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0608
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0609
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0610
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0611
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0612
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0613
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0614
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0615
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0616
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0617
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0618
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0619
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0620
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0621
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0622
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0623
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0624
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0625
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0626
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0627
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0628
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0629
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0630
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0631
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0632
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0633
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0634
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0635
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0636
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0637
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0638
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0639
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0640
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0641
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0642
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0643
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0644
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0645
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0646
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0647
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0648
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0649
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
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
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
