/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0950
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0951
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0952
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0953
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0954
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0955
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0956
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0957
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0958
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0959
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0960
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0961
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0962
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0963
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0964
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0965
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0966
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0967
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0968
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0969
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0970
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0971
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0972
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0973
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0974
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0975
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0976
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0977
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0978
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0979
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0980
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0981
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0982
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0983
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0984
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0985
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0986
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0987
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0988
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0989
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0990
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0991
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0992
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0993
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0994
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0995
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0996
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0997
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0998
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0999
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys019 : ∀ k ∈ keys019, Certified k := by
  apply certified_cons (by exact certified0950)
  apply certified_cons (by exact certified0951)
  apply certified_cons (by exact certified0952)
  apply certified_cons (by exact certified0953)
  apply certified_cons (by exact certified0954)
  apply certified_cons (by exact certified0955)
  apply certified_cons (by exact certified0956)
  apply certified_cons (by exact certified0957)
  apply certified_cons (by exact certified0958)
  apply certified_cons (by exact certified0959)
  apply certified_cons (by exact certified0960)
  apply certified_cons (by exact certified0961)
  apply certified_cons (by exact certified0962)
  apply certified_cons (by exact certified0963)
  apply certified_cons (by exact certified0964)
  apply certified_cons (by exact certified0965)
  apply certified_cons (by exact certified0966)
  apply certified_cons (by exact certified0967)
  apply certified_cons (by exact certified0968)
  apply certified_cons (by exact certified0969)
  apply certified_cons (by exact certified0970)
  apply certified_cons (by exact certified0971)
  apply certified_cons (by exact certified0972)
  apply certified_cons (by exact certified0973)
  apply certified_cons (by exact certified0974)
  apply certified_cons (by exact certified0975)
  apply certified_cons (by exact certified0976)
  apply certified_cons (by exact certified0977)
  apply certified_cons (by exact certified0978)
  apply certified_cons (by exact certified0979)
  apply certified_cons (by exact certified0980)
  apply certified_cons (by exact certified0981)
  apply certified_cons (by exact certified0982)
  apply certified_cons (by exact certified0983)
  apply certified_cons (by exact certified0984)
  apply certified_cons (by exact certified0985)
  apply certified_cons (by exact certified0986)
  apply certified_cons (by exact certified0987)
  apply certified_cons (by exact certified0988)
  apply certified_cons (by exact certified0989)
  apply certified_cons (by exact certified0990)
  apply certified_cons (by exact certified0991)
  apply certified_cons (by exact certified0992)
  apply certified_cons (by exact certified0993)
  apply certified_cons (by exact certified0994)
  apply certified_cons (by exact certified0995)
  apply certified_cons (by exact certified0996)
  apply certified_cons (by exact certified0997)
  apply certified_cons (by exact certified0998)
  apply certified_cons (by exact certified0999)
  simp
#print axioms certified_keys019
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
