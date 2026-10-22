/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1200
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1201
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1202
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1203
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1204
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1205
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1206
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1207
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1208
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1209
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1210
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1211
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1212
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1213
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1214
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1215
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1216
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1217
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1218
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1219
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1220
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1221
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1222
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1223
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1224
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1225
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1226
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1227
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1228
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1229
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1230
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1231
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1232
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1233
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1234
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1235
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1236
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1237
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1238
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1239
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1240
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1241
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1242
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1243
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1244
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1245
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1246
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1247
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1248
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1249
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys024 : ∀ k ∈ keys024, Certified k := by
  apply certified_cons (by exact certified1200)
  apply certified_cons (by exact certified1200swap)
  apply certified_cons (by exact certified1201)
  apply certified_cons (by exact certified1201swap)
  apply certified_cons (by exact certified1202)
  apply certified_cons (by exact certified1202swap)
  apply certified_cons (by exact certified1203)
  apply certified_cons (by exact certified1203swap)
  apply certified_cons (by exact certified1204)
  apply certified_cons (by exact certified1204swap)
  apply certified_cons (by exact certified1205)
  apply certified_cons (by exact certified1205swap)
  apply certified_cons (by exact certified1206)
  apply certified_cons (by exact certified1206swap)
  apply certified_cons (by exact certified1207)
  apply certified_cons (by exact certified1207swap)
  apply certified_cons (by exact certified1208)
  apply certified_cons (by exact certified1208swap)
  apply certified_cons (by exact certified1209)
  apply certified_cons (by exact certified1209swap)
  apply certified_cons (by exact certified1210)
  apply certified_cons (by exact certified1210swap)
  apply certified_cons (by exact certified1211)
  apply certified_cons (by exact certified1211swap)
  apply certified_cons (by exact certified1212)
  apply certified_cons (by exact certified1212swap)
  apply certified_cons (by exact certified1213)
  apply certified_cons (by exact certified1213swap)
  apply certified_cons (by exact certified1214)
  apply certified_cons (by exact certified1214swap)
  apply certified_cons (by exact certified1215)
  apply certified_cons (by exact certified1215swap)
  apply certified_cons (by exact certified1216)
  apply certified_cons (by exact certified1216swap)
  apply certified_cons (by exact certified1217)
  apply certified_cons (by exact certified1217swap)
  apply certified_cons (by exact certified1218)
  apply certified_cons (by exact certified1218swap)
  apply certified_cons (by exact certified1219)
  apply certified_cons (by exact certified1219swap)
  apply certified_cons (by exact certified1220)
  apply certified_cons (by exact certified1220swap)
  apply certified_cons (by exact certified1221)
  apply certified_cons (by exact certified1221swap)
  apply certified_cons (by exact certified1222)
  apply certified_cons (by exact certified1222swap)
  apply certified_cons (by exact certified1223)
  apply certified_cons (by exact certified1223swap)
  apply certified_cons (by exact certified1224)
  apply certified_cons (by exact certified1224swap)
  apply certified_cons (by exact certified1225)
  apply certified_cons (by exact certified1225swap)
  apply certified_cons (by exact certified1226)
  apply certified_cons (by exact certified1226swap)
  apply certified_cons (by exact certified1227)
  apply certified_cons (by exact certified1227swap)
  apply certified_cons (by exact certified1228)
  apply certified_cons (by exact certified1228swap)
  apply certified_cons (by exact certified1229)
  apply certified_cons (by exact certified1229swap)
  apply certified_cons (by exact certified1230)
  apply certified_cons (by exact certified1230swap)
  apply certified_cons (by exact certified1231)
  apply certified_cons (by exact certified1231swap)
  apply certified_cons (by exact certified1232)
  apply certified_cons (by exact certified1232swap)
  apply certified_cons (by exact certified1233)
  apply certified_cons (by exact certified1233swap)
  apply certified_cons (by exact certified1234)
  apply certified_cons (by exact certified1234swap)
  apply certified_cons (by exact certified1235)
  apply certified_cons (by exact certified1235swap)
  apply certified_cons (by exact certified1236)
  apply certified_cons (by exact certified1236swap)
  apply certified_cons (by exact certified1237)
  apply certified_cons (by exact certified1237swap)
  apply certified_cons (by exact certified1238)
  apply certified_cons (by exact certified1238swap)
  apply certified_cons (by exact certified1239)
  apply certified_cons (by exact certified1239swap)
  apply certified_cons (by exact certified1240)
  apply certified_cons (by exact certified1240swap)
  apply certified_cons (by exact certified1241)
  apply certified_cons (by exact certified1241swap)
  apply certified_cons (by exact certified1242)
  apply certified_cons (by exact certified1242swap)
  apply certified_cons (by exact certified1243)
  apply certified_cons (by exact certified1243swap)
  apply certified_cons (by exact certified1244)
  apply certified_cons (by exact certified1244swap)
  apply certified_cons (by exact certified1245)
  apply certified_cons (by exact certified1245swap)
  apply certified_cons (by exact certified1246)
  apply certified_cons (by exact certified1246swap)
  apply certified_cons (by exact certified1247)
  apply certified_cons (by exact certified1247swap)
  apply certified_cons (by exact certified1248)
  apply certified_cons (by exact certified1248swap)
  apply certified_cons (by exact certified1249)
  apply certified_cons (by exact certified1249swap)
  simp
#print axioms certified_keys024
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
