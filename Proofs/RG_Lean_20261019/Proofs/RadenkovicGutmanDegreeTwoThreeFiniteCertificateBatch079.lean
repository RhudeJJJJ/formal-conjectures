/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3950
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3951
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3952
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3953
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3954
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3955
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3956
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3957
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3958
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3959
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3960
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3961
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3962
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3963
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3964
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3965
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3966
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3967
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3968
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3969
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3970
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3971
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3972
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3973
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3974
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3975
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3976
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3977
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3978
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3979
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3980
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3981
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3982
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3983
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3984
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3985
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3986
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3987
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3988
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3989
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3990
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3991
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3992
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3993
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3994
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3995
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3996
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3997
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3998
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3999
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys079 : ∀ k ∈ keys079, Certified k := by
  apply certified_cons (by exact certified3950)
  apply certified_cons (by exact certified3950swap)
  apply certified_cons (by exact certified3951)
  apply certified_cons (by exact certified3951swap)
  apply certified_cons (by exact certified3952)
  apply certified_cons (by exact certified3952swap)
  apply certified_cons (by exact certified3953)
  apply certified_cons (by exact certified3953swap)
  apply certified_cons (by exact certified3954)
  apply certified_cons (by exact certified3954swap)
  apply certified_cons (by exact certified3955)
  apply certified_cons (by exact certified3955swap)
  apply certified_cons (by exact certified3956)
  apply certified_cons (by exact certified3956swap)
  apply certified_cons (by exact certified3957)
  apply certified_cons (by exact certified3957swap)
  apply certified_cons (by exact certified3958)
  apply certified_cons (by exact certified3958swap)
  apply certified_cons (by exact certified3959)
  apply certified_cons (by exact certified3959swap)
  apply certified_cons (by exact certified3960)
  apply certified_cons (by exact certified3960swap)
  apply certified_cons (by exact certified3961)
  apply certified_cons (by exact certified3961swap)
  apply certified_cons (by exact certified3962)
  apply certified_cons (by exact certified3962swap)
  apply certified_cons (by exact certified3963)
  apply certified_cons (by exact certified3963swap)
  apply certified_cons (by exact certified3964)
  apply certified_cons (by exact certified3964swap)
  apply certified_cons (by exact certified3965)
  apply certified_cons (by exact certified3965swap)
  apply certified_cons (by exact certified3966)
  apply certified_cons (by exact certified3966swap)
  apply certified_cons (by exact certified3967)
  apply certified_cons (by exact certified3967swap)
  apply certified_cons (by exact certified3968)
  apply certified_cons (by exact certified3968swap)
  apply certified_cons (by exact certified3969)
  apply certified_cons (by exact certified3969swap)
  apply certified_cons (by exact certified3970)
  apply certified_cons (by exact certified3970swap)
  apply certified_cons (by exact certified3971)
  apply certified_cons (by exact certified3971swap)
  apply certified_cons (by exact certified3972)
  apply certified_cons (by exact certified3972swap)
  apply certified_cons (by exact certified3973)
  apply certified_cons (by exact certified3973swap)
  apply certified_cons (by exact certified3974)
  apply certified_cons (by exact certified3974swap)
  apply certified_cons (by exact certified3975)
  apply certified_cons (by exact certified3975swap)
  apply certified_cons (by exact certified3976)
  apply certified_cons (by exact certified3976swap)
  apply certified_cons (by exact certified3977)
  apply certified_cons (by exact certified3977swap)
  apply certified_cons (by exact certified3978)
  apply certified_cons (by exact certified3978swap)
  apply certified_cons (by exact certified3979)
  apply certified_cons (by exact certified3979swap)
  apply certified_cons (by exact certified3980)
  apply certified_cons (by exact certified3980swap)
  apply certified_cons (by exact certified3981)
  apply certified_cons (by exact certified3981swap)
  apply certified_cons (by exact certified3982)
  apply certified_cons (by exact certified3982swap)
  apply certified_cons (by exact certified3983)
  apply certified_cons (by exact certified3983swap)
  apply certified_cons (by exact certified3984)
  apply certified_cons (by exact certified3984swap)
  apply certified_cons (by exact certified3985)
  apply certified_cons (by exact certified3985swap)
  apply certified_cons (by exact certified3986)
  apply certified_cons (by exact certified3986swap)
  apply certified_cons (by exact certified3987)
  apply certified_cons (by exact certified3987swap)
  apply certified_cons (by exact certified3988)
  apply certified_cons (by exact certified3988swap)
  apply certified_cons (by exact certified3989)
  apply certified_cons (by exact certified3989swap)
  apply certified_cons (by exact certified3990)
  apply certified_cons (by exact certified3990swap)
  apply certified_cons (by exact certified3991)
  apply certified_cons (by exact certified3991swap)
  apply certified_cons (by exact certified3992)
  apply certified_cons (by exact certified3992swap)
  apply certified_cons (by exact certified3993)
  apply certified_cons (by exact certified3993swap)
  apply certified_cons (by exact certified3994)
  apply certified_cons (by exact certified3994swap)
  apply certified_cons (by exact certified3995)
  apply certified_cons (by exact certified3995swap)
  apply certified_cons (by exact certified3996)
  apply certified_cons (by exact certified3996swap)
  apply certified_cons (by exact certified3997)
  apply certified_cons (by exact certified3997swap)
  apply certified_cons (by exact certified3998)
  apply certified_cons (by exact certified3998swap)
  apply certified_cons (by exact certified3999)
  apply certified_cons (by exact certified3999swap)
  simp
#print axioms certified_keys079
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
