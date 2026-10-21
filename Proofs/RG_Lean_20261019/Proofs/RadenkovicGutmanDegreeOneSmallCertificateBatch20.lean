/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1000
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1001
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1002
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1003
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1004
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1005
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1006
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1007
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1008
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1009
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1010
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1011
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1012
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1013
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1014
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1015
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1016
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1017
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1018
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1019
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1020
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1021
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1022
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1023
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1024
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1025
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1026
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1027
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1028
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1029
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1030
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1031
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1032
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1033
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1034
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1035
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1036
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1037
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1038
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1039
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1040
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1041
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1042
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1043
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1044
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1045
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1046
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1047
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1048
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1049
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys20 : ∀ k ∈ keys20, Certified k := by
  apply certified_cons (by exact certified1000)
  apply certified_cons (by exact certified1000swap)
  apply certified_cons (by exact certified1001)
  apply certified_cons (by exact certified1001swap)
  apply certified_cons (by exact certified1002)
  apply certified_cons (by exact certified1003)
  apply certified_cons (by exact certified1004)
  apply certified_cons (by exact certified1004swap)
  apply certified_cons (by exact certified1005)
  apply certified_cons (by exact certified1005swap)
  apply certified_cons (by exact certified1006)
  apply certified_cons (by exact certified1007)
  apply certified_cons (by exact certified1008)
  apply certified_cons (by exact certified1008swap)
  apply certified_cons (by exact certified1009)
  apply certified_cons (by exact certified1009swap)
  apply certified_cons (by exact certified1010)
  apply certified_cons (by exact certified1011)
  apply certified_cons (by exact certified1012)
  apply certified_cons (by exact certified1012swap)
  apply certified_cons (by exact certified1013)
  apply certified_cons (by exact certified1013swap)
  apply certified_cons (by exact certified1014)
  apply certified_cons (by exact certified1015)
  apply certified_cons (by exact certified1016)
  apply certified_cons (by exact certified1016swap)
  apply certified_cons (by exact certified1017)
  apply certified_cons (by exact certified1017swap)
  apply certified_cons (by exact certified1018)
  apply certified_cons (by exact certified1019)
  apply certified_cons (by exact certified1020)
  apply certified_cons (by exact certified1020swap)
  apply certified_cons (by exact certified1021)
  apply certified_cons (by exact certified1021swap)
  apply certified_cons (by exact certified1022)
  apply certified_cons (by exact certified1023)
  apply certified_cons (by exact certified1024)
  apply certified_cons (by exact certified1024swap)
  apply certified_cons (by exact certified1025)
  apply certified_cons (by exact certified1025swap)
  apply certified_cons (by exact certified1026)
  apply certified_cons (by exact certified1027)
  apply certified_cons (by exact certified1028)
  apply certified_cons (by exact certified1028swap)
  apply certified_cons (by exact certified1029)
  apply certified_cons (by exact certified1029swap)
  apply certified_cons (by exact certified1030)
  apply certified_cons (by exact certified1031)
  apply certified_cons (by exact certified1032)
  apply certified_cons (by exact certified1032swap)
  apply certified_cons (by exact certified1033)
  apply certified_cons (by exact certified1033swap)
  apply certified_cons (by exact certified1034)
  apply certified_cons (by exact certified1035)
  apply certified_cons (by exact certified1036)
  apply certified_cons (by exact certified1036swap)
  apply certified_cons (by exact certified1037)
  apply certified_cons (by exact certified1037swap)
  apply certified_cons (by exact certified1038)
  apply certified_cons (by exact certified1039)
  apply certified_cons (by exact certified1040)
  apply certified_cons (by exact certified1040swap)
  apply certified_cons (by exact certified1041)
  apply certified_cons (by exact certified1041swap)
  apply certified_cons (by exact certified1042)
  apply certified_cons (by exact certified1043)
  apply certified_cons (by exact certified1044)
  apply certified_cons (by exact certified1044swap)
  apply certified_cons (by exact certified1045)
  apply certified_cons (by exact certified1045swap)
  apply certified_cons (by exact certified1046)
  apply certified_cons (by exact certified1047)
  apply certified_cons (by exact certified1048)
  apply certified_cons (by exact certified1048swap)
  apply certified_cons (by exact certified1049)
  apply certified_cons (by exact certified1049swap)
  simp
#print axioms certified_keys20
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
