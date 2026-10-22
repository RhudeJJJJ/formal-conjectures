/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1100
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1101
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1102
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1103
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1104
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1105
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1106
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1107
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1108
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1109
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1110
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1111
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1112
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1113
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1114
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1115
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1116
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1117
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1118
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1119
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1120
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1121
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1122
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1123
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1124
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1125
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1126
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1127
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1128
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1129
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1130
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1131
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1132
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1133
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1134
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1135
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1136
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1137
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1138
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1139
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1140
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1141
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1142
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1143
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1144
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1145
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1146
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1147
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1148
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1149
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys022 : ∀ k ∈ keys022, Certified k := by
  apply certified_cons (by exact certified1100)
  apply certified_cons (by exact certified1100swap)
  apply certified_cons (by exact certified1101)
  apply certified_cons (by exact certified1101swap)
  apply certified_cons (by exact certified1102)
  apply certified_cons (by exact certified1102swap)
  apply certified_cons (by exact certified1103)
  apply certified_cons (by exact certified1103swap)
  apply certified_cons (by exact certified1104)
  apply certified_cons (by exact certified1104swap)
  apply certified_cons (by exact certified1105)
  apply certified_cons (by exact certified1105swap)
  apply certified_cons (by exact certified1106)
  apply certified_cons (by exact certified1106swap)
  apply certified_cons (by exact certified1107)
  apply certified_cons (by exact certified1107swap)
  apply certified_cons (by exact certified1108)
  apply certified_cons (by exact certified1108swap)
  apply certified_cons (by exact certified1109)
  apply certified_cons (by exact certified1109swap)
  apply certified_cons (by exact certified1110)
  apply certified_cons (by exact certified1110swap)
  apply certified_cons (by exact certified1111)
  apply certified_cons (by exact certified1111swap)
  apply certified_cons (by exact certified1112)
  apply certified_cons (by exact certified1112swap)
  apply certified_cons (by exact certified1113)
  apply certified_cons (by exact certified1113swap)
  apply certified_cons (by exact certified1114)
  apply certified_cons (by exact certified1114swap)
  apply certified_cons (by exact certified1115)
  apply certified_cons (by exact certified1115swap)
  apply certified_cons (by exact certified1116)
  apply certified_cons (by exact certified1116swap)
  apply certified_cons (by exact certified1117)
  apply certified_cons (by exact certified1117swap)
  apply certified_cons (by exact certified1118)
  apply certified_cons (by exact certified1118swap)
  apply certified_cons (by exact certified1119)
  apply certified_cons (by exact certified1119swap)
  apply certified_cons (by exact certified1120)
  apply certified_cons (by exact certified1120swap)
  apply certified_cons (by exact certified1121)
  apply certified_cons (by exact certified1121swap)
  apply certified_cons (by exact certified1122)
  apply certified_cons (by exact certified1122swap)
  apply certified_cons (by exact certified1123)
  apply certified_cons (by exact certified1123swap)
  apply certified_cons (by exact certified1124)
  apply certified_cons (by exact certified1124swap)
  apply certified_cons (by exact certified1125)
  apply certified_cons (by exact certified1125swap)
  apply certified_cons (by exact certified1126)
  apply certified_cons (by exact certified1126swap)
  apply certified_cons (by exact certified1127)
  apply certified_cons (by exact certified1127swap)
  apply certified_cons (by exact certified1128)
  apply certified_cons (by exact certified1128swap)
  apply certified_cons (by exact certified1129)
  apply certified_cons (by exact certified1129swap)
  apply certified_cons (by exact certified1130)
  apply certified_cons (by exact certified1130swap)
  apply certified_cons (by exact certified1131)
  apply certified_cons (by exact certified1131swap)
  apply certified_cons (by exact certified1132)
  apply certified_cons (by exact certified1132swap)
  apply certified_cons (by exact certified1133)
  apply certified_cons (by exact certified1133swap)
  apply certified_cons (by exact certified1134)
  apply certified_cons (by exact certified1134swap)
  apply certified_cons (by exact certified1135)
  apply certified_cons (by exact certified1135swap)
  apply certified_cons (by exact certified1136)
  apply certified_cons (by exact certified1136swap)
  apply certified_cons (by exact certified1137)
  apply certified_cons (by exact certified1137swap)
  apply certified_cons (by exact certified1138)
  apply certified_cons (by exact certified1138swap)
  apply certified_cons (by exact certified1139)
  apply certified_cons (by exact certified1139swap)
  apply certified_cons (by exact certified1140)
  apply certified_cons (by exact certified1140swap)
  apply certified_cons (by exact certified1141)
  apply certified_cons (by exact certified1141swap)
  apply certified_cons (by exact certified1142)
  apply certified_cons (by exact certified1142swap)
  apply certified_cons (by exact certified1143)
  apply certified_cons (by exact certified1143swap)
  apply certified_cons (by exact certified1144)
  apply certified_cons (by exact certified1144swap)
  apply certified_cons (by exact certified1145)
  apply certified_cons (by exact certified1145swap)
  apply certified_cons (by exact certified1146)
  apply certified_cons (by exact certified1146swap)
  apply certified_cons (by exact certified1147)
  apply certified_cons (by exact certified1147swap)
  apply certified_cons (by exact certified1148)
  apply certified_cons (by exact certified1148swap)
  apply certified_cons (by exact certified1149)
  apply certified_cons (by exact certified1149swap)
  simp
#print axioms certified_keys022
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
