/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0600
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0601
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0602
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0603
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0604
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0605
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0606
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0607
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0608
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0609
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0610
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0611
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0612
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0613
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0614
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0615
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0616
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0617
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0618
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0619
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0620
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0621
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0622
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0623
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0624
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0625
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0626
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0627
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0628
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0629
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0630
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0631
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0632
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0633
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0634
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0635
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0636
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0637
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0638
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0639
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0640
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0641
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0642
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0643
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0644
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0645
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0646
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0647
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0648
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0649
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys12 : ∀ k ∈ keys12, Certified k := by
  apply certified_cons (by exact certified0600)
  apply certified_cons (by exact certified0600swap)
  apply certified_cons (by exact certified0601)
  apply certified_cons (by exact certified0602)
  apply certified_cons (by exact certified0602swap)
  apply certified_cons (by exact certified0603)
  apply certified_cons (by exact certified0604)
  apply certified_cons (by exact certified0604swap)
  apply certified_cons (by exact certified0605)
  apply certified_cons (by exact certified0605swap)
  apply certified_cons (by exact certified0606)
  apply certified_cons (by exact certified0606swap)
  apply certified_cons (by exact certified0607)
  apply certified_cons (by exact certified0608)
  apply certified_cons (by exact certified0608swap)
  apply certified_cons (by exact certified0609)
  apply certified_cons (by exact certified0610)
  apply certified_cons (by exact certified0610swap)
  apply certified_cons (by exact certified0611)
  apply certified_cons (by exact certified0611swap)
  apply certified_cons (by exact certified0612)
  apply certified_cons (by exact certified0612swap)
  apply certified_cons (by exact certified0613)
  apply certified_cons (by exact certified0614)
  apply certified_cons (by exact certified0614swap)
  apply certified_cons (by exact certified0615)
  apply certified_cons (by exact certified0616)
  apply certified_cons (by exact certified0616swap)
  apply certified_cons (by exact certified0617)
  apply certified_cons (by exact certified0617swap)
  apply certified_cons (by exact certified0618)
  apply certified_cons (by exact certified0618swap)
  apply certified_cons (by exact certified0619)
  apply certified_cons (by exact certified0620)
  apply certified_cons (by exact certified0620swap)
  apply certified_cons (by exact certified0621)
  apply certified_cons (by exact certified0622)
  apply certified_cons (by exact certified0622swap)
  apply certified_cons (by exact certified0623)
  apply certified_cons (by exact certified0623swap)
  apply certified_cons (by exact certified0624)
  apply certified_cons (by exact certified0624swap)
  apply certified_cons (by exact certified0625)
  apply certified_cons (by exact certified0626)
  apply certified_cons (by exact certified0626swap)
  apply certified_cons (by exact certified0627)
  apply certified_cons (by exact certified0628)
  apply certified_cons (by exact certified0628swap)
  apply certified_cons (by exact certified0629)
  apply certified_cons (by exact certified0629swap)
  apply certified_cons (by exact certified0630)
  apply certified_cons (by exact certified0630swap)
  apply certified_cons (by exact certified0631)
  apply certified_cons (by exact certified0632)
  apply certified_cons (by exact certified0632swap)
  apply certified_cons (by exact certified0633)
  apply certified_cons (by exact certified0634)
  apply certified_cons (by exact certified0634swap)
  apply certified_cons (by exact certified0635)
  apply certified_cons (by exact certified0635swap)
  apply certified_cons (by exact certified0636)
  apply certified_cons (by exact certified0636swap)
  apply certified_cons (by exact certified0637)
  apply certified_cons (by exact certified0638)
  apply certified_cons (by exact certified0638swap)
  apply certified_cons (by exact certified0639)
  apply certified_cons (by exact certified0640)
  apply certified_cons (by exact certified0640swap)
  apply certified_cons (by exact certified0641)
  apply certified_cons (by exact certified0641swap)
  apply certified_cons (by exact certified0642)
  apply certified_cons (by exact certified0642swap)
  apply certified_cons (by exact certified0643)
  apply certified_cons (by exact certified0644)
  apply certified_cons (by exact certified0644swap)
  apply certified_cons (by exact certified0645)
  apply certified_cons (by exact certified0646)
  apply certified_cons (by exact certified0646swap)
  apply certified_cons (by exact certified0647)
  apply certified_cons (by exact certified0647swap)
  apply certified_cons (by exact certified0648)
  apply certified_cons (by exact certified0648swap)
  apply certified_cons (by exact certified0649)
  simp
#print axioms certified_keys12
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
