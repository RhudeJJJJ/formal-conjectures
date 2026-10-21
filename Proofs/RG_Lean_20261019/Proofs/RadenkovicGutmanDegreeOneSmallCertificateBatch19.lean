/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0950
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0951
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0952
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0953
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0954
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0955
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0956
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0957
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0958
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0959
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0960
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0961
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0962
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0963
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0964
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0965
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0966
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0967
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0968
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0969
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0970
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0971
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0972
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0973
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0974
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0975
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0976
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0977
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0978
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0979
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0980
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0981
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0982
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0983
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0984
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0985
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0986
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0987
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0988
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0989
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0990
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0991
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0992
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0993
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0994
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0995
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0996
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0997
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0998
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0999
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys19 : ∀ k ∈ keys19, Certified k := by
  apply certified_cons (by exact certified0950)
  apply certified_cons (by exact certified0951)
  apply certified_cons (by exact certified0952)
  apply certified_cons (by exact certified0952swap)
  apply certified_cons (by exact certified0953)
  apply certified_cons (by exact certified0953swap)
  apply certified_cons (by exact certified0954)
  apply certified_cons (by exact certified0955)
  apply certified_cons (by exact certified0956)
  apply certified_cons (by exact certified0956swap)
  apply certified_cons (by exact certified0957)
  apply certified_cons (by exact certified0957swap)
  apply certified_cons (by exact certified0958)
  apply certified_cons (by exact certified0959)
  apply certified_cons (by exact certified0960)
  apply certified_cons (by exact certified0960swap)
  apply certified_cons (by exact certified0961)
  apply certified_cons (by exact certified0961swap)
  apply certified_cons (by exact certified0962)
  apply certified_cons (by exact certified0963)
  apply certified_cons (by exact certified0964)
  apply certified_cons (by exact certified0964swap)
  apply certified_cons (by exact certified0965)
  apply certified_cons (by exact certified0965swap)
  apply certified_cons (by exact certified0966)
  apply certified_cons (by exact certified0967)
  apply certified_cons (by exact certified0968)
  apply certified_cons (by exact certified0968swap)
  apply certified_cons (by exact certified0969)
  apply certified_cons (by exact certified0969swap)
  apply certified_cons (by exact certified0970)
  apply certified_cons (by exact certified0971)
  apply certified_cons (by exact certified0972)
  apply certified_cons (by exact certified0972swap)
  apply certified_cons (by exact certified0973)
  apply certified_cons (by exact certified0973swap)
  apply certified_cons (by exact certified0974)
  apply certified_cons (by exact certified0975)
  apply certified_cons (by exact certified0976)
  apply certified_cons (by exact certified0976swap)
  apply certified_cons (by exact certified0977)
  apply certified_cons (by exact certified0977swap)
  apply certified_cons (by exact certified0978)
  apply certified_cons (by exact certified0979)
  apply certified_cons (by exact certified0980)
  apply certified_cons (by exact certified0980swap)
  apply certified_cons (by exact certified0981)
  apply certified_cons (by exact certified0981swap)
  apply certified_cons (by exact certified0982)
  apply certified_cons (by exact certified0983)
  apply certified_cons (by exact certified0984)
  apply certified_cons (by exact certified0984swap)
  apply certified_cons (by exact certified0985)
  apply certified_cons (by exact certified0985swap)
  apply certified_cons (by exact certified0986)
  apply certified_cons (by exact certified0987)
  apply certified_cons (by exact certified0988)
  apply certified_cons (by exact certified0988swap)
  apply certified_cons (by exact certified0989)
  apply certified_cons (by exact certified0989swap)
  apply certified_cons (by exact certified0990)
  apply certified_cons (by exact certified0991)
  apply certified_cons (by exact certified0992)
  apply certified_cons (by exact certified0992swap)
  apply certified_cons (by exact certified0993)
  apply certified_cons (by exact certified0993swap)
  apply certified_cons (by exact certified0994)
  apply certified_cons (by exact certified0995)
  apply certified_cons (by exact certified0996)
  apply certified_cons (by exact certified0996swap)
  apply certified_cons (by exact certified0997)
  apply certified_cons (by exact certified0997swap)
  apply certified_cons (by exact certified0998)
  apply certified_cons (by exact certified0999)
  simp
#print axioms certified_keys19
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
