/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3750
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3751
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3752
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3753
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3754
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3755
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3756
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3757
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3758
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3759
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3760
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3761
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3762
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3763
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3764
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3765
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3766
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3767
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3768
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3769
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3770
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3771
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3772
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3773
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3774
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3775
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3776
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3777
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3778
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3779
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3780
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3781
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3782
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3783
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3784
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3785
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3786
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3787
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3788
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3789
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3790
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3791
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3792
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3793
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3794
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3795
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3796
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3797
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3798
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3799
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys075 : ∀ k ∈ keys075, Certified k := by
  apply certified_cons (by exact certified3750)
  apply certified_cons (by exact certified3751)
  apply certified_cons (by exact certified3752)
  apply certified_cons (by exact certified3753)
  apply certified_cons (by exact certified3754)
  apply certified_cons (by exact certified3755)
  apply certified_cons (by exact certified3756)
  apply certified_cons (by exact certified3756swap)
  apply certified_cons (by exact certified3757)
  apply certified_cons (by exact certified3757swap)
  apply certified_cons (by exact certified3758)
  apply certified_cons (by exact certified3758swap)
  apply certified_cons (by exact certified3759)
  apply certified_cons (by exact certified3759swap)
  apply certified_cons (by exact certified3760)
  apply certified_cons (by exact certified3760swap)
  apply certified_cons (by exact certified3761)
  apply certified_cons (by exact certified3761swap)
  apply certified_cons (by exact certified3762)
  apply certified_cons (by exact certified3762swap)
  apply certified_cons (by exact certified3763)
  apply certified_cons (by exact certified3763swap)
  apply certified_cons (by exact certified3764)
  apply certified_cons (by exact certified3764swap)
  apply certified_cons (by exact certified3765)
  apply certified_cons (by exact certified3765swap)
  apply certified_cons (by exact certified3766)
  apply certified_cons (by exact certified3766swap)
  apply certified_cons (by exact certified3767)
  apply certified_cons (by exact certified3767swap)
  apply certified_cons (by exact certified3768)
  apply certified_cons (by exact certified3768swap)
  apply certified_cons (by exact certified3769)
  apply certified_cons (by exact certified3769swap)
  apply certified_cons (by exact certified3770)
  apply certified_cons (by exact certified3770swap)
  apply certified_cons (by exact certified3771)
  apply certified_cons (by exact certified3771swap)
  apply certified_cons (by exact certified3772)
  apply certified_cons (by exact certified3772swap)
  apply certified_cons (by exact certified3773)
  apply certified_cons (by exact certified3773swap)
  apply certified_cons (by exact certified3774)
  apply certified_cons (by exact certified3774swap)
  apply certified_cons (by exact certified3775)
  apply certified_cons (by exact certified3775swap)
  apply certified_cons (by exact certified3776)
  apply certified_cons (by exact certified3776swap)
  apply certified_cons (by exact certified3777)
  apply certified_cons (by exact certified3777swap)
  apply certified_cons (by exact certified3778)
  apply certified_cons (by exact certified3778swap)
  apply certified_cons (by exact certified3779)
  apply certified_cons (by exact certified3779swap)
  apply certified_cons (by exact certified3780)
  apply certified_cons (by exact certified3780swap)
  apply certified_cons (by exact certified3781)
  apply certified_cons (by exact certified3781swap)
  apply certified_cons (by exact certified3782)
  apply certified_cons (by exact certified3782swap)
  apply certified_cons (by exact certified3783)
  apply certified_cons (by exact certified3783swap)
  apply certified_cons (by exact certified3784)
  apply certified_cons (by exact certified3784swap)
  apply certified_cons (by exact certified3785)
  apply certified_cons (by exact certified3785swap)
  apply certified_cons (by exact certified3786)
  apply certified_cons (by exact certified3786swap)
  apply certified_cons (by exact certified3787)
  apply certified_cons (by exact certified3787swap)
  apply certified_cons (by exact certified3788)
  apply certified_cons (by exact certified3788swap)
  apply certified_cons (by exact certified3789)
  apply certified_cons (by exact certified3789swap)
  apply certified_cons (by exact certified3790)
  apply certified_cons (by exact certified3790swap)
  apply certified_cons (by exact certified3791)
  apply certified_cons (by exact certified3791swap)
  apply certified_cons (by exact certified3792)
  apply certified_cons (by exact certified3792swap)
  apply certified_cons (by exact certified3793)
  apply certified_cons (by exact certified3793swap)
  apply certified_cons (by exact certified3794)
  apply certified_cons (by exact certified3794swap)
  apply certified_cons (by exact certified3795)
  apply certified_cons (by exact certified3795swap)
  apply certified_cons (by exact certified3796)
  apply certified_cons (by exact certified3796swap)
  apply certified_cons (by exact certified3797)
  apply certified_cons (by exact certified3797swap)
  apply certified_cons (by exact certified3798)
  apply certified_cons (by exact certified3798swap)
  apply certified_cons (by exact certified3799)
  apply certified_cons (by exact certified3799swap)
  simp
#print axioms certified_keys075
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
