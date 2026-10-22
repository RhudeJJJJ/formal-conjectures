/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3650
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3651
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3652
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3653
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3654
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3655
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3656
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3657
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3658
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3659
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3660
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3661
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3662
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3663
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3664
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3665
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3666
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3667
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3668
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3669
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3670
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3671
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3672
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3673
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3674
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3675
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3676
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3677
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3678
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3679
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3680
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3681
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3682
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3683
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3684
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3685
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3686
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3687
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3688
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3689
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3690
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3691
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3692
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3693
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3694
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3695
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3696
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3697
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3698
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3699
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
