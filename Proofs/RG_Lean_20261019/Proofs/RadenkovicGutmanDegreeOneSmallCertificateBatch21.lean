/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1050
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1051
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1052
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1053
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1054
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1055
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1056
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1057
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1058
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1059
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1060
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1061
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1062
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1063
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1064
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1065
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1066
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1067
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1068
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1069
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1070
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1071
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1072
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1073
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1074
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1075
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1076
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1077
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1078
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1079
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1080
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1081
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1082
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1083
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1084
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1085
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1086
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1087
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1088
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1089
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1090
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1091
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1092
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1093
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1094
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1095
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1096
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1097
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1098
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1099
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys21 : ∀ k ∈ keys21, Certified k := by
  apply certified_cons (by exact certified1050)
  apply certified_cons (by exact certified1051)
  apply certified_cons (by exact certified1052)
  apply certified_cons (by exact certified1052swap)
  apply certified_cons (by exact certified1053)
  apply certified_cons (by exact certified1053swap)
  apply certified_cons (by exact certified1054)
  apply certified_cons (by exact certified1055)
  apply certified_cons (by exact certified1056)
  apply certified_cons (by exact certified1056swap)
  apply certified_cons (by exact certified1057)
  apply certified_cons (by exact certified1057swap)
  apply certified_cons (by exact certified1058)
  apply certified_cons (by exact certified1059)
  apply certified_cons (by exact certified1060)
  apply certified_cons (by exact certified1060swap)
  apply certified_cons (by exact certified1061)
  apply certified_cons (by exact certified1061swap)
  apply certified_cons (by exact certified1062)
  apply certified_cons (by exact certified1063)
  apply certified_cons (by exact certified1064)
  apply certified_cons (by exact certified1064swap)
  apply certified_cons (by exact certified1065)
  apply certified_cons (by exact certified1065swap)
  apply certified_cons (by exact certified1066)
  apply certified_cons (by exact certified1067)
  apply certified_cons (by exact certified1068)
  apply certified_cons (by exact certified1068swap)
  apply certified_cons (by exact certified1069)
  apply certified_cons (by exact certified1069swap)
  apply certified_cons (by exact certified1070)
  apply certified_cons (by exact certified1071)
  apply certified_cons (by exact certified1072)
  apply certified_cons (by exact certified1072swap)
  apply certified_cons (by exact certified1073)
  apply certified_cons (by exact certified1073swap)
  apply certified_cons (by exact certified1074)
  apply certified_cons (by exact certified1075)
  apply certified_cons (by exact certified1076)
  apply certified_cons (by exact certified1076swap)
  apply certified_cons (by exact certified1077)
  apply certified_cons (by exact certified1077swap)
  apply certified_cons (by exact certified1078)
  apply certified_cons (by exact certified1079)
  apply certified_cons (by exact certified1080)
  apply certified_cons (by exact certified1080swap)
  apply certified_cons (by exact certified1081)
  apply certified_cons (by exact certified1081swap)
  apply certified_cons (by exact certified1082)
  apply certified_cons (by exact certified1083)
  apply certified_cons (by exact certified1084)
  apply certified_cons (by exact certified1084swap)
  apply certified_cons (by exact certified1085)
  apply certified_cons (by exact certified1085swap)
  apply certified_cons (by exact certified1086)
  apply certified_cons (by exact certified1087)
  apply certified_cons (by exact certified1088)
  apply certified_cons (by exact certified1088swap)
  apply certified_cons (by exact certified1089)
  apply certified_cons (by exact certified1089swap)
  apply certified_cons (by exact certified1090)
  apply certified_cons (by exact certified1091)
  apply certified_cons (by exact certified1092)
  apply certified_cons (by exact certified1092swap)
  apply certified_cons (by exact certified1093)
  apply certified_cons (by exact certified1093swap)
  apply certified_cons (by exact certified1094)
  apply certified_cons (by exact certified1095)
  apply certified_cons (by exact certified1096)
  apply certified_cons (by exact certified1096swap)
  apply certified_cons (by exact certified1097)
  apply certified_cons (by exact certified1097swap)
  apply certified_cons (by exact certified1098)
  apply certified_cons (by exact certified1099)
  simp
#print axioms certified_keys21
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
