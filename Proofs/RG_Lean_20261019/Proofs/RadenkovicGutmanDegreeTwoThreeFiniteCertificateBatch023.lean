/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1150
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1151
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1152
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1153
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1154
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1155
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1156
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1157
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1158
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1159
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1160
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1161
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1162
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1163
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1164
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1165
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1166
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1167
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1168
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1169
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1170
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1171
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1172
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1173
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1174
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1175
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1176
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1177
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1178
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1179
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1180
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1181
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1182
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1183
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1184
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1185
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1186
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1187
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1188
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1189
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1190
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1191
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1192
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1193
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1194
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1195
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1196
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1197
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1198
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1199
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys023 : ∀ k ∈ keys023, Certified k := by
  apply certified_cons (by exact certified1150)
  apply certified_cons (by exact certified1150swap)
  apply certified_cons (by exact certified1151)
  apply certified_cons (by exact certified1151swap)
  apply certified_cons (by exact certified1152)
  apply certified_cons (by exact certified1152swap)
  apply certified_cons (by exact certified1153)
  apply certified_cons (by exact certified1153swap)
  apply certified_cons (by exact certified1154)
  apply certified_cons (by exact certified1154swap)
  apply certified_cons (by exact certified1155)
  apply certified_cons (by exact certified1155swap)
  apply certified_cons (by exact certified1156)
  apply certified_cons (by exact certified1156swap)
  apply certified_cons (by exact certified1157)
  apply certified_cons (by exact certified1157swap)
  apply certified_cons (by exact certified1158)
  apply certified_cons (by exact certified1158swap)
  apply certified_cons (by exact certified1159)
  apply certified_cons (by exact certified1159swap)
  apply certified_cons (by exact certified1160)
  apply certified_cons (by exact certified1160swap)
  apply certified_cons (by exact certified1161)
  apply certified_cons (by exact certified1161swap)
  apply certified_cons (by exact certified1162)
  apply certified_cons (by exact certified1162swap)
  apply certified_cons (by exact certified1163)
  apply certified_cons (by exact certified1163swap)
  apply certified_cons (by exact certified1164)
  apply certified_cons (by exact certified1164swap)
  apply certified_cons (by exact certified1165)
  apply certified_cons (by exact certified1165swap)
  apply certified_cons (by exact certified1166)
  apply certified_cons (by exact certified1166swap)
  apply certified_cons (by exact certified1167)
  apply certified_cons (by exact certified1167swap)
  apply certified_cons (by exact certified1168)
  apply certified_cons (by exact certified1168swap)
  apply certified_cons (by exact certified1169)
  apply certified_cons (by exact certified1169swap)
  apply certified_cons (by exact certified1170)
  apply certified_cons (by exact certified1170swap)
  apply certified_cons (by exact certified1171)
  apply certified_cons (by exact certified1171swap)
  apply certified_cons (by exact certified1172)
  apply certified_cons (by exact certified1172swap)
  apply certified_cons (by exact certified1173)
  apply certified_cons (by exact certified1173swap)
  apply certified_cons (by exact certified1174)
  apply certified_cons (by exact certified1174swap)
  apply certified_cons (by exact certified1175)
  apply certified_cons (by exact certified1175swap)
  apply certified_cons (by exact certified1176)
  apply certified_cons (by exact certified1176swap)
  apply certified_cons (by exact certified1177)
  apply certified_cons (by exact certified1177swap)
  apply certified_cons (by exact certified1178)
  apply certified_cons (by exact certified1178swap)
  apply certified_cons (by exact certified1179)
  apply certified_cons (by exact certified1179swap)
  apply certified_cons (by exact certified1180)
  apply certified_cons (by exact certified1180swap)
  apply certified_cons (by exact certified1181)
  apply certified_cons (by exact certified1181swap)
  apply certified_cons (by exact certified1182)
  apply certified_cons (by exact certified1182swap)
  apply certified_cons (by exact certified1183)
  apply certified_cons (by exact certified1183swap)
  apply certified_cons (by exact certified1184)
  apply certified_cons (by exact certified1184swap)
  apply certified_cons (by exact certified1185)
  apply certified_cons (by exact certified1185swap)
  apply certified_cons (by exact certified1186)
  apply certified_cons (by exact certified1186swap)
  apply certified_cons (by exact certified1187)
  apply certified_cons (by exact certified1187swap)
  apply certified_cons (by exact certified1188)
  apply certified_cons (by exact certified1188swap)
  apply certified_cons (by exact certified1189)
  apply certified_cons (by exact certified1189swap)
  apply certified_cons (by exact certified1190)
  apply certified_cons (by exact certified1190swap)
  apply certified_cons (by exact certified1191)
  apply certified_cons (by exact certified1191swap)
  apply certified_cons (by exact certified1192)
  apply certified_cons (by exact certified1192swap)
  apply certified_cons (by exact certified1193)
  apply certified_cons (by exact certified1193swap)
  apply certified_cons (by exact certified1194)
  apply certified_cons (by exact certified1194swap)
  apply certified_cons (by exact certified1195)
  apply certified_cons (by exact certified1195swap)
  apply certified_cons (by exact certified1196)
  apply certified_cons (by exact certified1196swap)
  apply certified_cons (by exact certified1197)
  apply certified_cons (by exact certified1197swap)
  apply certified_cons (by exact certified1198)
  apply certified_cons (by exact certified1198swap)
  apply certified_cons (by exact certified1199)
  apply certified_cons (by exact certified1199swap)
  simp
#print axioms certified_keys023
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
