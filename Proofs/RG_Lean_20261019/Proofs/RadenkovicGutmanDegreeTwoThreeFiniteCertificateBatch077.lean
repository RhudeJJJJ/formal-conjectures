/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3850
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3851
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3852
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3853
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3854
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3855
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3856
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3857
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3858
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3859
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3860
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3861
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3862
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3863
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3864
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3865
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3866
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3867
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3868
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3869
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3870
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3871
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3872
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3873
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3874
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3875
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3876
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3877
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3878
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3879
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3880
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3881
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3882
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3883
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3884
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3885
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3886
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3887
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3888
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3889
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3890
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3891
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3892
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3893
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3894
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3895
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3896
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3897
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3898
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3899
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys077 : ∀ k ∈ keys077, Certified k := by
  apply certified_cons (by exact certified3850)
  apply certified_cons (by exact certified3850swap)
  apply certified_cons (by exact certified3851)
  apply certified_cons (by exact certified3851swap)
  apply certified_cons (by exact certified3852)
  apply certified_cons (by exact certified3852swap)
  apply certified_cons (by exact certified3853)
  apply certified_cons (by exact certified3853swap)
  apply certified_cons (by exact certified3854)
  apply certified_cons (by exact certified3854swap)
  apply certified_cons (by exact certified3855)
  apply certified_cons (by exact certified3855swap)
  apply certified_cons (by exact certified3856)
  apply certified_cons (by exact certified3856swap)
  apply certified_cons (by exact certified3857)
  apply certified_cons (by exact certified3857swap)
  apply certified_cons (by exact certified3858)
  apply certified_cons (by exact certified3858swap)
  apply certified_cons (by exact certified3859)
  apply certified_cons (by exact certified3859swap)
  apply certified_cons (by exact certified3860)
  apply certified_cons (by exact certified3860swap)
  apply certified_cons (by exact certified3861)
  apply certified_cons (by exact certified3861swap)
  apply certified_cons (by exact certified3862)
  apply certified_cons (by exact certified3862swap)
  apply certified_cons (by exact certified3863)
  apply certified_cons (by exact certified3863swap)
  apply certified_cons (by exact certified3864)
  apply certified_cons (by exact certified3864swap)
  apply certified_cons (by exact certified3865)
  apply certified_cons (by exact certified3865swap)
  apply certified_cons (by exact certified3866)
  apply certified_cons (by exact certified3866swap)
  apply certified_cons (by exact certified3867)
  apply certified_cons (by exact certified3867swap)
  apply certified_cons (by exact certified3868)
  apply certified_cons (by exact certified3868swap)
  apply certified_cons (by exact certified3869)
  apply certified_cons (by exact certified3869swap)
  apply certified_cons (by exact certified3870)
  apply certified_cons (by exact certified3870swap)
  apply certified_cons (by exact certified3871)
  apply certified_cons (by exact certified3871swap)
  apply certified_cons (by exact certified3872)
  apply certified_cons (by exact certified3872swap)
  apply certified_cons (by exact certified3873)
  apply certified_cons (by exact certified3873swap)
  apply certified_cons (by exact certified3874)
  apply certified_cons (by exact certified3874swap)
  apply certified_cons (by exact certified3875)
  apply certified_cons (by exact certified3875swap)
  apply certified_cons (by exact certified3876)
  apply certified_cons (by exact certified3876swap)
  apply certified_cons (by exact certified3877)
  apply certified_cons (by exact certified3877swap)
  apply certified_cons (by exact certified3878)
  apply certified_cons (by exact certified3878swap)
  apply certified_cons (by exact certified3879)
  apply certified_cons (by exact certified3879swap)
  apply certified_cons (by exact certified3880)
  apply certified_cons (by exact certified3880swap)
  apply certified_cons (by exact certified3881)
  apply certified_cons (by exact certified3881swap)
  apply certified_cons (by exact certified3882)
  apply certified_cons (by exact certified3882swap)
  apply certified_cons (by exact certified3883)
  apply certified_cons (by exact certified3883swap)
  apply certified_cons (by exact certified3884)
  apply certified_cons (by exact certified3884swap)
  apply certified_cons (by exact certified3885)
  apply certified_cons (by exact certified3885swap)
  apply certified_cons (by exact certified3886)
  apply certified_cons (by exact certified3886swap)
  apply certified_cons (by exact certified3887)
  apply certified_cons (by exact certified3887swap)
  apply certified_cons (by exact certified3888)
  apply certified_cons (by exact certified3888swap)
  apply certified_cons (by exact certified3889)
  apply certified_cons (by exact certified3889swap)
  apply certified_cons (by exact certified3890)
  apply certified_cons (by exact certified3890swap)
  apply certified_cons (by exact certified3891)
  apply certified_cons (by exact certified3891swap)
  apply certified_cons (by exact certified3892)
  apply certified_cons (by exact certified3892swap)
  apply certified_cons (by exact certified3893)
  apply certified_cons (by exact certified3893swap)
  apply certified_cons (by exact certified3894)
  apply certified_cons (by exact certified3894swap)
  apply certified_cons (by exact certified3895)
  apply certified_cons (by exact certified3895swap)
  apply certified_cons (by exact certified3896)
  apply certified_cons (by exact certified3896swap)
  apply certified_cons (by exact certified3897)
  apply certified_cons (by exact certified3897swap)
  apply certified_cons (by exact certified3898)
  apply certified_cons (by exact certified3898swap)
  apply certified_cons (by exact certified3899)
  apply certified_cons (by exact certified3899swap)
  simp
#print axioms certified_keys077
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
