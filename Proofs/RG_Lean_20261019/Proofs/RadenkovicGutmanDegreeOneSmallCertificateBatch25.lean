/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1250
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1251
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1252
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1253
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1254
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1255
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1256
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1257
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1258
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1259
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1260
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1261
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1262
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1263
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1264
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1265
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1266
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1267
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1268
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1269
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1270
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1271
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1272
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1273
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1274
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1275
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1276
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1277
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1278
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1279
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1280
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1281
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1282
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1283
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1284
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1285
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1286
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1287
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1288
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1289
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1290
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1291
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1292
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1293
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1294
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1295
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1296
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1297
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1298
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1299
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys25 : ∀ k ∈ keys25, Certified k := by
  apply certified_cons (by exact certified1250)
  apply certified_cons (by exact certified1250swap)
  apply certified_cons (by exact certified1251)
  apply certified_cons (by exact certified1252)
  apply certified_cons (by exact certified1252swap)
  apply certified_cons (by exact certified1253)
  apply certified_cons (by exact certified1254)
  apply certified_cons (by exact certified1254swap)
  apply certified_cons (by exact certified1255)
  apply certified_cons (by exact certified1256)
  apply certified_cons (by exact certified1256swap)
  apply certified_cons (by exact certified1257)
  apply certified_cons (by exact certified1258)
  apply certified_cons (by exact certified1258swap)
  apply certified_cons (by exact certified1259)
  apply certified_cons (by exact certified1260)
  apply certified_cons (by exact certified1260swap)
  apply certified_cons (by exact certified1261)
  apply certified_cons (by exact certified1262)
  apply certified_cons (by exact certified1262swap)
  apply certified_cons (by exact certified1263)
  apply certified_cons (by exact certified1264)
  apply certified_cons (by exact certified1264swap)
  apply certified_cons (by exact certified1265)
  apply certified_cons (by exact certified1266)
  apply certified_cons (by exact certified1266swap)
  apply certified_cons (by exact certified1267)
  apply certified_cons (by exact certified1268)
  apply certified_cons (by exact certified1268swap)
  apply certified_cons (by exact certified1269)
  apply certified_cons (by exact certified1270)
  apply certified_cons (by exact certified1270swap)
  apply certified_cons (by exact certified1271)
  apply certified_cons (by exact certified1272)
  apply certified_cons (by exact certified1272swap)
  apply certified_cons (by exact certified1273)
  apply certified_cons (by exact certified1274)
  apply certified_cons (by exact certified1274swap)
  apply certified_cons (by exact certified1275)
  apply certified_cons (by exact certified1276)
  apply certified_cons (by exact certified1276swap)
  apply certified_cons (by exact certified1277)
  apply certified_cons (by exact certified1278)
  apply certified_cons (by exact certified1278swap)
  apply certified_cons (by exact certified1279)
  apply certified_cons (by exact certified1280)
  apply certified_cons (by exact certified1280swap)
  apply certified_cons (by exact certified1281)
  apply certified_cons (by exact certified1282)
  apply certified_cons (by exact certified1282swap)
  apply certified_cons (by exact certified1283)
  apply certified_cons (by exact certified1284)
  apply certified_cons (by exact certified1284swap)
  apply certified_cons (by exact certified1285)
  apply certified_cons (by exact certified1286)
  apply certified_cons (by exact certified1286swap)
  apply certified_cons (by exact certified1287)
  apply certified_cons (by exact certified1288)
  apply certified_cons (by exact certified1288swap)
  apply certified_cons (by exact certified1289)
  apply certified_cons (by exact certified1290)
  apply certified_cons (by exact certified1290swap)
  apply certified_cons (by exact certified1291)
  apply certified_cons (by exact certified1292)
  apply certified_cons (by exact certified1292swap)
  apply certified_cons (by exact certified1293)
  apply certified_cons (by exact certified1294)
  apply certified_cons (by exact certified1294swap)
  apply certified_cons (by exact certified1295)
  apply certified_cons (by exact certified1296)
  apply certified_cons (by exact certified1296swap)
  apply certified_cons (by exact certified1297)
  apply certified_cons (by exact certified1298)
  apply certified_cons (by exact certified1298swap)
  apply certified_cons (by exact certified1299)
  simp
#print axioms certified_keys25
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
