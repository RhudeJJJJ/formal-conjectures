/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3600
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3601
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3602
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3603
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3604
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3605
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3606
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3607
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3608
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3609
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3610
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3611
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3612
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3613
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3614
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3615
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3616
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3617
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3618
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3619
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3620
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3621
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3622
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3623
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3624
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3625
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3626
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3627
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3628
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3629
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3630
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3631
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3632
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3633
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3634
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3635
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3636
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3637
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3638
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3639
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3640
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3641
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3642
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3643
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3644
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3645
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3646
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3647
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3648
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3649
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys072 : ∀ k ∈ keys072, Certified k := by
  apply certified_cons (by exact certified3600)
  apply certified_cons (by exact certified3600swap)
  apply certified_cons (by exact certified3601)
  apply certified_cons (by exact certified3601swap)
  apply certified_cons (by exact certified3602)
  apply certified_cons (by exact certified3602swap)
  apply certified_cons (by exact certified3603)
  apply certified_cons (by exact certified3603swap)
  apply certified_cons (by exact certified3604)
  apply certified_cons (by exact certified3604swap)
  apply certified_cons (by exact certified3605)
  apply certified_cons (by exact certified3605swap)
  apply certified_cons (by exact certified3606)
  apply certified_cons (by exact certified3606swap)
  apply certified_cons (by exact certified3607)
  apply certified_cons (by exact certified3607swap)
  apply certified_cons (by exact certified3608)
  apply certified_cons (by exact certified3608swap)
  apply certified_cons (by exact certified3609)
  apply certified_cons (by exact certified3609swap)
  apply certified_cons (by exact certified3610)
  apply certified_cons (by exact certified3610swap)
  apply certified_cons (by exact certified3611)
  apply certified_cons (by exact certified3611swap)
  apply certified_cons (by exact certified3612)
  apply certified_cons (by exact certified3612swap)
  apply certified_cons (by exact certified3613)
  apply certified_cons (by exact certified3613swap)
  apply certified_cons (by exact certified3614)
  apply certified_cons (by exact certified3614swap)
  apply certified_cons (by exact certified3615)
  apply certified_cons (by exact certified3615swap)
  apply certified_cons (by exact certified3616)
  apply certified_cons (by exact certified3616swap)
  apply certified_cons (by exact certified3617)
  apply certified_cons (by exact certified3617swap)
  apply certified_cons (by exact certified3618)
  apply certified_cons (by exact certified3618swap)
  apply certified_cons (by exact certified3619)
  apply certified_cons (by exact certified3619swap)
  apply certified_cons (by exact certified3620)
  apply certified_cons (by exact certified3620swap)
  apply certified_cons (by exact certified3621)
  apply certified_cons (by exact certified3621swap)
  apply certified_cons (by exact certified3622)
  apply certified_cons (by exact certified3622swap)
  apply certified_cons (by exact certified3623)
  apply certified_cons (by exact certified3623swap)
  apply certified_cons (by exact certified3624)
  apply certified_cons (by exact certified3624swap)
  apply certified_cons (by exact certified3625)
  apply certified_cons (by exact certified3625swap)
  apply certified_cons (by exact certified3626)
  apply certified_cons (by exact certified3626swap)
  apply certified_cons (by exact certified3627)
  apply certified_cons (by exact certified3627swap)
  apply certified_cons (by exact certified3628)
  apply certified_cons (by exact certified3628swap)
  apply certified_cons (by exact certified3629)
  apply certified_cons (by exact certified3629swap)
  apply certified_cons (by exact certified3630)
  apply certified_cons (by exact certified3630swap)
  apply certified_cons (by exact certified3631)
  apply certified_cons (by exact certified3631swap)
  apply certified_cons (by exact certified3632)
  apply certified_cons (by exact certified3632swap)
  apply certified_cons (by exact certified3633)
  apply certified_cons (by exact certified3633swap)
  apply certified_cons (by exact certified3634)
  apply certified_cons (by exact certified3634swap)
  apply certified_cons (by exact certified3635)
  apply certified_cons (by exact certified3635swap)
  apply certified_cons (by exact certified3636)
  apply certified_cons (by exact certified3636swap)
  apply certified_cons (by exact certified3637)
  apply certified_cons (by exact certified3637swap)
  apply certified_cons (by exact certified3638)
  apply certified_cons (by exact certified3638swap)
  apply certified_cons (by exact certified3639)
  apply certified_cons (by exact certified3639swap)
  apply certified_cons (by exact certified3640)
  apply certified_cons (by exact certified3640swap)
  apply certified_cons (by exact certified3641)
  apply certified_cons (by exact certified3641swap)
  apply certified_cons (by exact certified3642)
  apply certified_cons (by exact certified3642swap)
  apply certified_cons (by exact certified3643)
  apply certified_cons (by exact certified3643swap)
  apply certified_cons (by exact certified3644)
  apply certified_cons (by exact certified3644swap)
  apply certified_cons (by exact certified3645)
  apply certified_cons (by exact certified3645swap)
  apply certified_cons (by exact certified3646)
  apply certified_cons (by exact certified3646swap)
  apply certified_cons (by exact certified3647)
  apply certified_cons (by exact certified3647swap)
  apply certified_cons (by exact certified3648)
  apply certified_cons (by exact certified3648swap)
  apply certified_cons (by exact certified3649)
  apply certified_cons (by exact certified3649swap)
  simp
#print axioms certified_keys072
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
