/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1050
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1051
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1052
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1053
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1054
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1055
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1056
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1057
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1058
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1059
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1060
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1061
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1062
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1063
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1064
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1065
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1066
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1067
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1068
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1069
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1070
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1071
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1072
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1073
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1074
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1075
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1076
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1077
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1078
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1079
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1080
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1081
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1082
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1083
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1084
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1085
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1086
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1087
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1088
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1089
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1090
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1091
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1092
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1093
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1094
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1095
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1096
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1097
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1098
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1099
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys021 : ∀ k ∈ keys021, Certified k := by
  apply certified_cons (by exact certified1050)
  apply certified_cons (by exact certified1050swap)
  apply certified_cons (by exact certified1051)
  apply certified_cons (by exact certified1051swap)
  apply certified_cons (by exact certified1052)
  apply certified_cons (by exact certified1052swap)
  apply certified_cons (by exact certified1053)
  apply certified_cons (by exact certified1053swap)
  apply certified_cons (by exact certified1054)
  apply certified_cons (by exact certified1054swap)
  apply certified_cons (by exact certified1055)
  apply certified_cons (by exact certified1055swap)
  apply certified_cons (by exact certified1056)
  apply certified_cons (by exact certified1056swap)
  apply certified_cons (by exact certified1057)
  apply certified_cons (by exact certified1057swap)
  apply certified_cons (by exact certified1058)
  apply certified_cons (by exact certified1058swap)
  apply certified_cons (by exact certified1059)
  apply certified_cons (by exact certified1059swap)
  apply certified_cons (by exact certified1060)
  apply certified_cons (by exact certified1060swap)
  apply certified_cons (by exact certified1061)
  apply certified_cons (by exact certified1061swap)
  apply certified_cons (by exact certified1062)
  apply certified_cons (by exact certified1062swap)
  apply certified_cons (by exact certified1063)
  apply certified_cons (by exact certified1063swap)
  apply certified_cons (by exact certified1064)
  apply certified_cons (by exact certified1064swap)
  apply certified_cons (by exact certified1065)
  apply certified_cons (by exact certified1065swap)
  apply certified_cons (by exact certified1066)
  apply certified_cons (by exact certified1066swap)
  apply certified_cons (by exact certified1067)
  apply certified_cons (by exact certified1067swap)
  apply certified_cons (by exact certified1068)
  apply certified_cons (by exact certified1068swap)
  apply certified_cons (by exact certified1069)
  apply certified_cons (by exact certified1069swap)
  apply certified_cons (by exact certified1070)
  apply certified_cons (by exact certified1070swap)
  apply certified_cons (by exact certified1071)
  apply certified_cons (by exact certified1071swap)
  apply certified_cons (by exact certified1072)
  apply certified_cons (by exact certified1072swap)
  apply certified_cons (by exact certified1073)
  apply certified_cons (by exact certified1073swap)
  apply certified_cons (by exact certified1074)
  apply certified_cons (by exact certified1074swap)
  apply certified_cons (by exact certified1075)
  apply certified_cons (by exact certified1075swap)
  apply certified_cons (by exact certified1076)
  apply certified_cons (by exact certified1076swap)
  apply certified_cons (by exact certified1077)
  apply certified_cons (by exact certified1077swap)
  apply certified_cons (by exact certified1078)
  apply certified_cons (by exact certified1078swap)
  apply certified_cons (by exact certified1079)
  apply certified_cons (by exact certified1079swap)
  apply certified_cons (by exact certified1080)
  apply certified_cons (by exact certified1080swap)
  apply certified_cons (by exact certified1081)
  apply certified_cons (by exact certified1081swap)
  apply certified_cons (by exact certified1082)
  apply certified_cons (by exact certified1082swap)
  apply certified_cons (by exact certified1083)
  apply certified_cons (by exact certified1083swap)
  apply certified_cons (by exact certified1084)
  apply certified_cons (by exact certified1084swap)
  apply certified_cons (by exact certified1085)
  apply certified_cons (by exact certified1085swap)
  apply certified_cons (by exact certified1086)
  apply certified_cons (by exact certified1086swap)
  apply certified_cons (by exact certified1087)
  apply certified_cons (by exact certified1087swap)
  apply certified_cons (by exact certified1088)
  apply certified_cons (by exact certified1088swap)
  apply certified_cons (by exact certified1089)
  apply certified_cons (by exact certified1089swap)
  apply certified_cons (by exact certified1090)
  apply certified_cons (by exact certified1090swap)
  apply certified_cons (by exact certified1091)
  apply certified_cons (by exact certified1091swap)
  apply certified_cons (by exact certified1092)
  apply certified_cons (by exact certified1092swap)
  apply certified_cons (by exact certified1093)
  apply certified_cons (by exact certified1093swap)
  apply certified_cons (by exact certified1094)
  apply certified_cons (by exact certified1094swap)
  apply certified_cons (by exact certified1095)
  apply certified_cons (by exact certified1095swap)
  apply certified_cons (by exact certified1096)
  apply certified_cons (by exact certified1096swap)
  apply certified_cons (by exact certified1097)
  apply certified_cons (by exact certified1097swap)
  apply certified_cons (by exact certified1098)
  apply certified_cons (by exact certified1098swap)
  apply certified_cons (by exact certified1099)
  apply certified_cons (by exact certified1099swap)
  simp
#print axioms certified_keys021
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
