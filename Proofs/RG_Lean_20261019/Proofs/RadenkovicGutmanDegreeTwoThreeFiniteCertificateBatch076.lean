/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3800
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3801
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3802
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3803
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3804
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3805
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3806
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3807
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3808
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3809
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3810
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3811
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3812
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3813
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3814
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3815
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3816
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3817
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3818
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3819
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3820
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3821
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3822
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3823
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3824
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3825
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3826
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3827
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3828
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3829
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3830
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3831
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3832
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3833
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3834
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3835
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3836
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3837
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3838
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3839
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3840
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3841
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3842
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3843
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3844
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3845
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3846
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3847
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3848
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3849
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
