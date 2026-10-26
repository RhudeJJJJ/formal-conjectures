/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3650
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3651
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3652
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3653
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3654
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3655
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3656
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3657
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3658
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3659
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3660
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3661
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3662
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3663
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3664
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3665
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3666
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3667
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3668
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3669
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3670
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3671
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3672
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3673
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3674
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3675
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3676
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3677
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3678
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3679
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3680
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3681
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3682
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3683
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3684
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3685
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3686
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3687
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3688
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3689
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3690
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3691
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3692
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3693
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3694
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3695
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3696
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3697
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3698
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3699
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys073 : ∀ k ∈ keys073, Certified k := by
  apply certified_cons (by exact certified3650)
  apply certified_cons (by exact certified3650swap)
  apply certified_cons (by exact certified3651)
  apply certified_cons (by exact certified3651swap)
  apply certified_cons (by exact certified3652)
  apply certified_cons (by exact certified3652swap)
  apply certified_cons (by exact certified3653)
  apply certified_cons (by exact certified3653swap)
  apply certified_cons (by exact certified3654)
  apply certified_cons (by exact certified3654swap)
  apply certified_cons (by exact certified3655)
  apply certified_cons (by exact certified3655swap)
  apply certified_cons (by exact certified3656)
  apply certified_cons (by exact certified3656swap)
  apply certified_cons (by exact certified3657)
  apply certified_cons (by exact certified3657swap)
  apply certified_cons (by exact certified3658)
  apply certified_cons (by exact certified3658swap)
  apply certified_cons (by exact certified3659)
  apply certified_cons (by exact certified3659swap)
  apply certified_cons (by exact certified3660)
  apply certified_cons (by exact certified3660swap)
  apply certified_cons (by exact certified3661)
  apply certified_cons (by exact certified3661swap)
  apply certified_cons (by exact certified3662)
  apply certified_cons (by exact certified3662swap)
  apply certified_cons (by exact certified3663)
  apply certified_cons (by exact certified3663swap)
  apply certified_cons (by exact certified3664)
  apply certified_cons (by exact certified3664swap)
  apply certified_cons (by exact certified3665)
  apply certified_cons (by exact certified3665swap)
  apply certified_cons (by exact certified3666)
  apply certified_cons (by exact certified3666swap)
  apply certified_cons (by exact certified3667)
  apply certified_cons (by exact certified3667swap)
  apply certified_cons (by exact certified3668)
  apply certified_cons (by exact certified3668swap)
  apply certified_cons (by exact certified3669)
  apply certified_cons (by exact certified3669swap)
  apply certified_cons (by exact certified3670)
  apply certified_cons (by exact certified3670swap)
  apply certified_cons (by exact certified3671)
  apply certified_cons (by exact certified3671swap)
  apply certified_cons (by exact certified3672)
  apply certified_cons (by exact certified3672swap)
  apply certified_cons (by exact certified3673)
  apply certified_cons (by exact certified3673swap)
  apply certified_cons (by exact certified3674)
  apply certified_cons (by exact certified3674swap)
  apply certified_cons (by exact certified3675)
  apply certified_cons (by exact certified3675swap)
  apply certified_cons (by exact certified3676)
  apply certified_cons (by exact certified3676swap)
  apply certified_cons (by exact certified3677)
  apply certified_cons (by exact certified3677swap)
  apply certified_cons (by exact certified3678)
  apply certified_cons (by exact certified3678swap)
  apply certified_cons (by exact certified3679)
  apply certified_cons (by exact certified3679swap)
  apply certified_cons (by exact certified3680)
  apply certified_cons (by exact certified3680swap)
  apply certified_cons (by exact certified3681)
  apply certified_cons (by exact certified3681swap)
  apply certified_cons (by exact certified3682)
  apply certified_cons (by exact certified3682swap)
  apply certified_cons (by exact certified3683)
  apply certified_cons (by exact certified3683swap)
  apply certified_cons (by exact certified3684)
  apply certified_cons (by exact certified3684swap)
  apply certified_cons (by exact certified3685)
  apply certified_cons (by exact certified3685swap)
  apply certified_cons (by exact certified3686)
  apply certified_cons (by exact certified3686swap)
  apply certified_cons (by exact certified3687)
  apply certified_cons (by exact certified3687swap)
  apply certified_cons (by exact certified3688)
  apply certified_cons (by exact certified3688swap)
  apply certified_cons (by exact certified3689)
  apply certified_cons (by exact certified3689swap)
  apply certified_cons (by exact certified3690)
  apply certified_cons (by exact certified3690swap)
  apply certified_cons (by exact certified3691)
  apply certified_cons (by exact certified3691swap)
  apply certified_cons (by exact certified3692)
  apply certified_cons (by exact certified3692swap)
  apply certified_cons (by exact certified3693)
  apply certified_cons (by exact certified3693swap)
  apply certified_cons (by exact certified3694)
  apply certified_cons (by exact certified3694swap)
  apply certified_cons (by exact certified3695)
  apply certified_cons (by exact certified3695swap)
  apply certified_cons (by exact certified3696)
  apply certified_cons (by exact certified3696swap)
  apply certified_cons (by exact certified3697)
  apply certified_cons (by exact certified3697swap)
  apply certified_cons (by exact certified3698)
  apply certified_cons (by exact certified3698swap)
  apply certified_cons (by exact certified3699)
  apply certified_cons (by exact certified3699swap)
  simp
#print axioms certified_keys073
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
