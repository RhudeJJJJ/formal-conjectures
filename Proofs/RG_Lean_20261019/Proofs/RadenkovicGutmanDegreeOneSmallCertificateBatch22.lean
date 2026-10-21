/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1100
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1101
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1102
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1103
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1104
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1105
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1106
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1107
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1108
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1109
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1110
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1111
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1112
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1113
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1114
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1115
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1116
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1117
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1118
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1119
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1120
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1121
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1122
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1123
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1124
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1125
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1126
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1127
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1128
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1129
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1130
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1131
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1132
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1133
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1134
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1135
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1136
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1137
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1138
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1139
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1140
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1141
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1142
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1143
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1144
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1145
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1146
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1147
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1148
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1149
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys22 : ∀ k ∈ keys22, Certified k := by
  apply certified_cons (by exact certified1100)
  apply certified_cons (by exact certified1100swap)
  apply certified_cons (by exact certified1101)
  apply certified_cons (by exact certified1101swap)
  apply certified_cons (by exact certified1102)
  apply certified_cons (by exact certified1103)
  apply certified_cons (by exact certified1104)
  apply certified_cons (by exact certified1104swap)
  apply certified_cons (by exact certified1105)
  apply certified_cons (by exact certified1105swap)
  apply certified_cons (by exact certified1106)
  apply certified_cons (by exact certified1107)
  apply certified_cons (by exact certified1108)
  apply certified_cons (by exact certified1108swap)
  apply certified_cons (by exact certified1109)
  apply certified_cons (by exact certified1109swap)
  apply certified_cons (by exact certified1110)
  apply certified_cons (by exact certified1111)
  apply certified_cons (by exact certified1112)
  apply certified_cons (by exact certified1112swap)
  apply certified_cons (by exact certified1113)
  apply certified_cons (by exact certified1113swap)
  apply certified_cons (by exact certified1114)
  apply certified_cons (by exact certified1115)
  apply certified_cons (by exact certified1116)
  apply certified_cons (by exact certified1116swap)
  apply certified_cons (by exact certified1117)
  apply certified_cons (by exact certified1117swap)
  apply certified_cons (by exact certified1118)
  apply certified_cons (by exact certified1119)
  apply certified_cons (by exact certified1120)
  apply certified_cons (by exact certified1120swap)
  apply certified_cons (by exact certified1121)
  apply certified_cons (by exact certified1121swap)
  apply certified_cons (by exact certified1122)
  apply certified_cons (by exact certified1123)
  apply certified_cons (by exact certified1124)
  apply certified_cons (by exact certified1124swap)
  apply certified_cons (by exact certified1125)
  apply certified_cons (by exact certified1125swap)
  apply certified_cons (by exact certified1126)
  apply certified_cons (by exact certified1127)
  apply certified_cons (by exact certified1128)
  apply certified_cons (by exact certified1128swap)
  apply certified_cons (by exact certified1129)
  apply certified_cons (by exact certified1129swap)
  apply certified_cons (by exact certified1130)
  apply certified_cons (by exact certified1131)
  apply certified_cons (by exact certified1132)
  apply certified_cons (by exact certified1132swap)
  apply certified_cons (by exact certified1133)
  apply certified_cons (by exact certified1133swap)
  apply certified_cons (by exact certified1134)
  apply certified_cons (by exact certified1135)
  apply certified_cons (by exact certified1136)
  apply certified_cons (by exact certified1136swap)
  apply certified_cons (by exact certified1137)
  apply certified_cons (by exact certified1137swap)
  apply certified_cons (by exact certified1138)
  apply certified_cons (by exact certified1139)
  apply certified_cons (by exact certified1140)
  apply certified_cons (by exact certified1140swap)
  apply certified_cons (by exact certified1141)
  apply certified_cons (by exact certified1141swap)
  apply certified_cons (by exact certified1142)
  apply certified_cons (by exact certified1143)
  apply certified_cons (by exact certified1144)
  apply certified_cons (by exact certified1144swap)
  apply certified_cons (by exact certified1145)
  apply certified_cons (by exact certified1145swap)
  apply certified_cons (by exact certified1146)
  apply certified_cons (by exact certified1147)
  apply certified_cons (by exact certified1148)
  apply certified_cons (by exact certified1148swap)
  apply certified_cons (by exact certified1149)
  apply certified_cons (by exact certified1149swap)
  simp
#print axioms certified_keys22
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
