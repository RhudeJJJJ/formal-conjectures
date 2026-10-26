/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3800
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3801
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3802
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3803
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3804
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3805
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3806
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3807
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3808
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3809
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3810
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3811
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3812
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3813
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3814
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3815
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3816
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3817
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3818
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3819
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3820
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3821
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3822
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3823
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3824
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3825
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3826
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3827
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3828
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3829
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3830
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3831
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3832
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3833
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3834
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3835
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3836
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3837
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3838
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3839
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3840
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3841
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3842
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3843
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3844
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3845
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3846
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3847
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3848
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase3849
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys076 : ∀ k ∈ keys076, Certified k := by
  apply certified_cons (by exact certified3800)
  apply certified_cons (by exact certified3800swap)
  apply certified_cons (by exact certified3801)
  apply certified_cons (by exact certified3801swap)
  apply certified_cons (by exact certified3802)
  apply certified_cons (by exact certified3802swap)
  apply certified_cons (by exact certified3803)
  apply certified_cons (by exact certified3803swap)
  apply certified_cons (by exact certified3804)
  apply certified_cons (by exact certified3804swap)
  apply certified_cons (by exact certified3805)
  apply certified_cons (by exact certified3805swap)
  apply certified_cons (by exact certified3806)
  apply certified_cons (by exact certified3806swap)
  apply certified_cons (by exact certified3807)
  apply certified_cons (by exact certified3807swap)
  apply certified_cons (by exact certified3808)
  apply certified_cons (by exact certified3808swap)
  apply certified_cons (by exact certified3809)
  apply certified_cons (by exact certified3809swap)
  apply certified_cons (by exact certified3810)
  apply certified_cons (by exact certified3810swap)
  apply certified_cons (by exact certified3811)
  apply certified_cons (by exact certified3811swap)
  apply certified_cons (by exact certified3812)
  apply certified_cons (by exact certified3812swap)
  apply certified_cons (by exact certified3813)
  apply certified_cons (by exact certified3813swap)
  apply certified_cons (by exact certified3814)
  apply certified_cons (by exact certified3814swap)
  apply certified_cons (by exact certified3815)
  apply certified_cons (by exact certified3815swap)
  apply certified_cons (by exact certified3816)
  apply certified_cons (by exact certified3816swap)
  apply certified_cons (by exact certified3817)
  apply certified_cons (by exact certified3817swap)
  apply certified_cons (by exact certified3818)
  apply certified_cons (by exact certified3818swap)
  apply certified_cons (by exact certified3819)
  apply certified_cons (by exact certified3819swap)
  apply certified_cons (by exact certified3820)
  apply certified_cons (by exact certified3820swap)
  apply certified_cons (by exact certified3821)
  apply certified_cons (by exact certified3821swap)
  apply certified_cons (by exact certified3822)
  apply certified_cons (by exact certified3822swap)
  apply certified_cons (by exact certified3823)
  apply certified_cons (by exact certified3823swap)
  apply certified_cons (by exact certified3824)
  apply certified_cons (by exact certified3824swap)
  apply certified_cons (by exact certified3825)
  apply certified_cons (by exact certified3825swap)
  apply certified_cons (by exact certified3826)
  apply certified_cons (by exact certified3826swap)
  apply certified_cons (by exact certified3827)
  apply certified_cons (by exact certified3827swap)
  apply certified_cons (by exact certified3828)
  apply certified_cons (by exact certified3828swap)
  apply certified_cons (by exact certified3829)
  apply certified_cons (by exact certified3829swap)
  apply certified_cons (by exact certified3830)
  apply certified_cons (by exact certified3830swap)
  apply certified_cons (by exact certified3831)
  apply certified_cons (by exact certified3831swap)
  apply certified_cons (by exact certified3832)
  apply certified_cons (by exact certified3832swap)
  apply certified_cons (by exact certified3833)
  apply certified_cons (by exact certified3833swap)
  apply certified_cons (by exact certified3834)
  apply certified_cons (by exact certified3834swap)
  apply certified_cons (by exact certified3835)
  apply certified_cons (by exact certified3835swap)
  apply certified_cons (by exact certified3836)
  apply certified_cons (by exact certified3836swap)
  apply certified_cons (by exact certified3837)
  apply certified_cons (by exact certified3837swap)
  apply certified_cons (by exact certified3838)
  apply certified_cons (by exact certified3838swap)
  apply certified_cons (by exact certified3839)
  apply certified_cons (by exact certified3839swap)
  apply certified_cons (by exact certified3840)
  apply certified_cons (by exact certified3840swap)
  apply certified_cons (by exact certified3841)
  apply certified_cons (by exact certified3841swap)
  apply certified_cons (by exact certified3842)
  apply certified_cons (by exact certified3842swap)
  apply certified_cons (by exact certified3843)
  apply certified_cons (by exact certified3843swap)
  apply certified_cons (by exact certified3844)
  apply certified_cons (by exact certified3844swap)
  apply certified_cons (by exact certified3845)
  apply certified_cons (by exact certified3845swap)
  apply certified_cons (by exact certified3846)
  apply certified_cons (by exact certified3846swap)
  apply certified_cons (by exact certified3847)
  apply certified_cons (by exact certified3847swap)
  apply certified_cons (by exact certified3848)
  apply certified_cons (by exact certified3848swap)
  apply certified_cons (by exact certified3849)
  apply certified_cons (by exact certified3849swap)
  simp
#print axioms certified_keys076
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
