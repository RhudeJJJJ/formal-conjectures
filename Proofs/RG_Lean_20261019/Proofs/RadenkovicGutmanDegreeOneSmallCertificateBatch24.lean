/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1200
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1201
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1202
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1203
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1204
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1205
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1206
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1207
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1208
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1209
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1210
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1211
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1212
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1213
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1214
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1215
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1216
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1217
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1218
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1219
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1220
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1221
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1222
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1223
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1224
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1225
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1226
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1227
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1228
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1229
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1230
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1231
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1232
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1233
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1234
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1235
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1236
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1237
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1238
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1239
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1240
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1241
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1242
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1243
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1244
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1245
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1246
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1247
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1248
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1249
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys24 : ∀ k ∈ keys24, Certified k := by
  apply certified_cons (by exact certified1200)
  apply certified_cons (by exact certified1200swap)
  apply certified_cons (by exact certified1201)
  apply certified_cons (by exact certified1202)
  apply certified_cons (by exact certified1202swap)
  apply certified_cons (by exact certified1203)
  apply certified_cons (by exact certified1204)
  apply certified_cons (by exact certified1204swap)
  apply certified_cons (by exact certified1205)
  apply certified_cons (by exact certified1206)
  apply certified_cons (by exact certified1206swap)
  apply certified_cons (by exact certified1207)
  apply certified_cons (by exact certified1208)
  apply certified_cons (by exact certified1208swap)
  apply certified_cons (by exact certified1209)
  apply certified_cons (by exact certified1210)
  apply certified_cons (by exact certified1210swap)
  apply certified_cons (by exact certified1211)
  apply certified_cons (by exact certified1212)
  apply certified_cons (by exact certified1212swap)
  apply certified_cons (by exact certified1213)
  apply certified_cons (by exact certified1214)
  apply certified_cons (by exact certified1214swap)
  apply certified_cons (by exact certified1215)
  apply certified_cons (by exact certified1216)
  apply certified_cons (by exact certified1216swap)
  apply certified_cons (by exact certified1217)
  apply certified_cons (by exact certified1218)
  apply certified_cons (by exact certified1218swap)
  apply certified_cons (by exact certified1219)
  apply certified_cons (by exact certified1220)
  apply certified_cons (by exact certified1220swap)
  apply certified_cons (by exact certified1221)
  apply certified_cons (by exact certified1222)
  apply certified_cons (by exact certified1222swap)
  apply certified_cons (by exact certified1223)
  apply certified_cons (by exact certified1224)
  apply certified_cons (by exact certified1224swap)
  apply certified_cons (by exact certified1225)
  apply certified_cons (by exact certified1226)
  apply certified_cons (by exact certified1226swap)
  apply certified_cons (by exact certified1227)
  apply certified_cons (by exact certified1228)
  apply certified_cons (by exact certified1228swap)
  apply certified_cons (by exact certified1229)
  apply certified_cons (by exact certified1230)
  apply certified_cons (by exact certified1230swap)
  apply certified_cons (by exact certified1231)
  apply certified_cons (by exact certified1232)
  apply certified_cons (by exact certified1232swap)
  apply certified_cons (by exact certified1233)
  apply certified_cons (by exact certified1234)
  apply certified_cons (by exact certified1234swap)
  apply certified_cons (by exact certified1235)
  apply certified_cons (by exact certified1236)
  apply certified_cons (by exact certified1236swap)
  apply certified_cons (by exact certified1237)
  apply certified_cons (by exact certified1238)
  apply certified_cons (by exact certified1238swap)
  apply certified_cons (by exact certified1239)
  apply certified_cons (by exact certified1240)
  apply certified_cons (by exact certified1240swap)
  apply certified_cons (by exact certified1241)
  apply certified_cons (by exact certified1242)
  apply certified_cons (by exact certified1242swap)
  apply certified_cons (by exact certified1243)
  apply certified_cons (by exact certified1244)
  apply certified_cons (by exact certified1244swap)
  apply certified_cons (by exact certified1245)
  apply certified_cons (by exact certified1246)
  apply certified_cons (by exact certified1246swap)
  apply certified_cons (by exact certified1247)
  apply certified_cons (by exact certified1248)
  apply certified_cons (by exact certified1248swap)
  apply certified_cons (by exact certified1249)
  simp
#print axioms certified_keys24
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
