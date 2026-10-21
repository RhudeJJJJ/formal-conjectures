/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1150
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1151
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1152
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1153
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1154
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1155
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1156
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1157
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1158
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1159
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1160
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1161
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1162
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1163
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1164
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1165
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1166
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1167
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1168
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1169
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1170
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1171
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1172
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1173
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1174
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1175
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1176
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1177
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1178
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1179
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1180
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1181
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1182
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1183
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1184
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1185
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1186
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1187
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1188
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1189
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1190
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1191
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1192
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1193
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1194
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1195
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1196
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1197
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1198
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1199
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys23 : ∀ k ∈ keys23, Certified k := by
  apply certified_cons (by exact certified1150)
  apply certified_cons (by exact certified1151)
  apply certified_cons (by exact certified1152)
  apply certified_cons (by exact certified1152swap)
  apply certified_cons (by exact certified1153)
  apply certified_cons (by exact certified1153swap)
  apply certified_cons (by exact certified1154)
  apply certified_cons (by exact certified1155)
  apply certified_cons (by exact certified1156)
  apply certified_cons (by exact certified1156swap)
  apply certified_cons (by exact certified1157)
  apply certified_cons (by exact certified1157swap)
  apply certified_cons (by exact certified1158)
  apply certified_cons (by exact certified1159)
  apply certified_cons (by exact certified1160)
  apply certified_cons (by exact certified1160swap)
  apply certified_cons (by exact certified1161)
  apply certified_cons (by exact certified1161swap)
  apply certified_cons (by exact certified1162)
  apply certified_cons (by exact certified1163)
  apply certified_cons (by exact certified1164)
  apply certified_cons (by exact certified1164swap)
  apply certified_cons (by exact certified1165)
  apply certified_cons (by exact certified1165swap)
  apply certified_cons (by exact certified1166)
  apply certified_cons (by exact certified1167)
  apply certified_cons (by exact certified1168)
  apply certified_cons (by exact certified1168swap)
  apply certified_cons (by exact certified1169)
  apply certified_cons (by exact certified1169swap)
  apply certified_cons (by exact certified1170)
  apply certified_cons (by exact certified1171)
  apply certified_cons (by exact certified1172)
  apply certified_cons (by exact certified1172swap)
  apply certified_cons (by exact certified1173)
  apply certified_cons (by exact certified1173swap)
  apply certified_cons (by exact certified1174)
  apply certified_cons (by exact certified1175)
  apply certified_cons (by exact certified1176)
  apply certified_cons (by exact certified1176swap)
  apply certified_cons (by exact certified1177)
  apply certified_cons (by exact certified1177swap)
  apply certified_cons (by exact certified1178)
  apply certified_cons (by exact certified1179)
  apply certified_cons (by exact certified1180)
  apply certified_cons (by exact certified1180swap)
  apply certified_cons (by exact certified1181)
  apply certified_cons (by exact certified1181swap)
  apply certified_cons (by exact certified1182)
  apply certified_cons (by exact certified1183)
  apply certified_cons (by exact certified1184)
  apply certified_cons (by exact certified1184swap)
  apply certified_cons (by exact certified1185)
  apply certified_cons (by exact certified1185swap)
  apply certified_cons (by exact certified1186)
  apply certified_cons (by exact certified1187)
  apply certified_cons (by exact certified1188)
  apply certified_cons (by exact certified1188swap)
  apply certified_cons (by exact certified1189)
  apply certified_cons (by exact certified1189swap)
  apply certified_cons (by exact certified1190)
  apply certified_cons (by exact certified1191)
  apply certified_cons (by exact certified1192)
  apply certified_cons (by exact certified1192swap)
  apply certified_cons (by exact certified1193)
  apply certified_cons (by exact certified1193swap)
  apply certified_cons (by exact certified1194)
  apply certified_cons (by exact certified1195)
  apply certified_cons (by exact certified1196)
  apply certified_cons (by exact certified1196swap)
  apply certified_cons (by exact certified1197)
  apply certified_cons (by exact certified1198)
  apply certified_cons (by exact certified1198swap)
  apply certified_cons (by exact certified1199)
  simp
#print axioms certified_keys23
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
