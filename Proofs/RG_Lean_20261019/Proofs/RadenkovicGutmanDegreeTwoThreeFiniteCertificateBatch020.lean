/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1000
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1001
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1002
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1003
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1004
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1005
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1006
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1007
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1008
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1009
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1010
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1011
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1012
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1013
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1014
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1015
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1016
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1017
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1018
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1019
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1020
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1021
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1022
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1023
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1024
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1025
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1026
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1027
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1028
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1029
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1030
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1031
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1032
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1033
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1034
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1035
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1036
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1037
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1038
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1039
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1040
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1041
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1042
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1043
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1044
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1045
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1046
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1047
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1048
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1049
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys020 : ∀ k ∈ keys020, Certified k := by
  apply certified_cons (by exact certified1000)
  apply certified_cons (by exact certified1001)
  apply certified_cons (by exact certified1002)
  apply certified_cons (by exact certified1003)
  apply certified_cons (by exact certified1004)
  apply certified_cons (by exact certified1005)
  apply certified_cons (by exact certified1006)
  apply certified_cons (by exact certified1007)
  apply certified_cons (by exact certified1008)
  apply certified_cons (by exact certified1009)
  apply certified_cons (by exact certified1010)
  apply certified_cons (by exact certified1011)
  apply certified_cons (by exact certified1012)
  apply certified_cons (by exact certified1013)
  apply certified_cons (by exact certified1014)
  apply certified_cons (by exact certified1015)
  apply certified_cons (by exact certified1016)
  apply certified_cons (by exact certified1017)
  apply certified_cons (by exact certified1018)
  apply certified_cons (by exact certified1019)
  apply certified_cons (by exact certified1020)
  apply certified_cons (by exact certified1021)
  apply certified_cons (by exact certified1021swap)
  apply certified_cons (by exact certified1022)
  apply certified_cons (by exact certified1022swap)
  apply certified_cons (by exact certified1023)
  apply certified_cons (by exact certified1023swap)
  apply certified_cons (by exact certified1024)
  apply certified_cons (by exact certified1024swap)
  apply certified_cons (by exact certified1025)
  apply certified_cons (by exact certified1025swap)
  apply certified_cons (by exact certified1026)
  apply certified_cons (by exact certified1026swap)
  apply certified_cons (by exact certified1027)
  apply certified_cons (by exact certified1027swap)
  apply certified_cons (by exact certified1028)
  apply certified_cons (by exact certified1028swap)
  apply certified_cons (by exact certified1029)
  apply certified_cons (by exact certified1029swap)
  apply certified_cons (by exact certified1030)
  apply certified_cons (by exact certified1030swap)
  apply certified_cons (by exact certified1031)
  apply certified_cons (by exact certified1031swap)
  apply certified_cons (by exact certified1032)
  apply certified_cons (by exact certified1032swap)
  apply certified_cons (by exact certified1033)
  apply certified_cons (by exact certified1033swap)
  apply certified_cons (by exact certified1034)
  apply certified_cons (by exact certified1034swap)
  apply certified_cons (by exact certified1035)
  apply certified_cons (by exact certified1035swap)
  apply certified_cons (by exact certified1036)
  apply certified_cons (by exact certified1036swap)
  apply certified_cons (by exact certified1037)
  apply certified_cons (by exact certified1037swap)
  apply certified_cons (by exact certified1038)
  apply certified_cons (by exact certified1038swap)
  apply certified_cons (by exact certified1039)
  apply certified_cons (by exact certified1039swap)
  apply certified_cons (by exact certified1040)
  apply certified_cons (by exact certified1040swap)
  apply certified_cons (by exact certified1041)
  apply certified_cons (by exact certified1041swap)
  apply certified_cons (by exact certified1042)
  apply certified_cons (by exact certified1042swap)
  apply certified_cons (by exact certified1043)
  apply certified_cons (by exact certified1043swap)
  apply certified_cons (by exact certified1044)
  apply certified_cons (by exact certified1044swap)
  apply certified_cons (by exact certified1045)
  apply certified_cons (by exact certified1045swap)
  apply certified_cons (by exact certified1046)
  apply certified_cons (by exact certified1046swap)
  apply certified_cons (by exact certified1047)
  apply certified_cons (by exact certified1047swap)
  apply certified_cons (by exact certified1048)
  apply certified_cons (by exact certified1048swap)
  apply certified_cons (by exact certified1049)
  apply certified_cons (by exact certified1049swap)
  simp
#print axioms certified_keys020
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
