/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1250
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1251
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1252
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1253
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1254
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1255
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1256
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1257
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1258
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1259
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1260
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1261
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1262
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1263
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1264
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1265
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1266
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1267
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1268
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1269
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1270
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1271
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1272
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1273
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1274
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1275
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1276
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1277
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1278
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1279
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1280
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1281
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1282
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1283
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1284
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1285
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1286
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1287
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1288
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1289
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1290
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1291
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1292
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1293
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1294
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1295
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1296
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1297
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1298
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1299
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys025 : ∀ k ∈ keys025, Certified k := by
  apply certified_cons (by exact certified1250)
  apply certified_cons (by exact certified1250swap)
  apply certified_cons (by exact certified1251)
  apply certified_cons (by exact certified1251swap)
  apply certified_cons (by exact certified1252)
  apply certified_cons (by exact certified1252swap)
  apply certified_cons (by exact certified1253)
  apply certified_cons (by exact certified1253swap)
  apply certified_cons (by exact certified1254)
  apply certified_cons (by exact certified1254swap)
  apply certified_cons (by exact certified1255)
  apply certified_cons (by exact certified1255swap)
  apply certified_cons (by exact certified1256)
  apply certified_cons (by exact certified1256swap)
  apply certified_cons (by exact certified1257)
  apply certified_cons (by exact certified1257swap)
  apply certified_cons (by exact certified1258)
  apply certified_cons (by exact certified1258swap)
  apply certified_cons (by exact certified1259)
  apply certified_cons (by exact certified1259swap)
  apply certified_cons (by exact certified1260)
  apply certified_cons (by exact certified1260swap)
  apply certified_cons (by exact certified1261)
  apply certified_cons (by exact certified1261swap)
  apply certified_cons (by exact certified1262)
  apply certified_cons (by exact certified1262swap)
  apply certified_cons (by exact certified1263)
  apply certified_cons (by exact certified1263swap)
  apply certified_cons (by exact certified1264)
  apply certified_cons (by exact certified1264swap)
  apply certified_cons (by exact certified1265)
  apply certified_cons (by exact certified1265swap)
  apply certified_cons (by exact certified1266)
  apply certified_cons (by exact certified1266swap)
  apply certified_cons (by exact certified1267)
  apply certified_cons (by exact certified1267swap)
  apply certified_cons (by exact certified1268)
  apply certified_cons (by exact certified1268swap)
  apply certified_cons (by exact certified1269)
  apply certified_cons (by exact certified1269swap)
  apply certified_cons (by exact certified1270)
  apply certified_cons (by exact certified1270swap)
  apply certified_cons (by exact certified1271)
  apply certified_cons (by exact certified1271swap)
  apply certified_cons (by exact certified1272)
  apply certified_cons (by exact certified1272swap)
  apply certified_cons (by exact certified1273)
  apply certified_cons (by exact certified1273swap)
  apply certified_cons (by exact certified1274)
  apply certified_cons (by exact certified1274swap)
  apply certified_cons (by exact certified1275)
  apply certified_cons (by exact certified1275swap)
  apply certified_cons (by exact certified1276)
  apply certified_cons (by exact certified1276swap)
  apply certified_cons (by exact certified1277)
  apply certified_cons (by exact certified1277swap)
  apply certified_cons (by exact certified1278)
  apply certified_cons (by exact certified1278swap)
  apply certified_cons (by exact certified1279)
  apply certified_cons (by exact certified1279swap)
  apply certified_cons (by exact certified1280)
  apply certified_cons (by exact certified1280swap)
  apply certified_cons (by exact certified1281)
  apply certified_cons (by exact certified1281swap)
  apply certified_cons (by exact certified1282)
  apply certified_cons (by exact certified1282swap)
  apply certified_cons (by exact certified1283)
  apply certified_cons (by exact certified1283swap)
  apply certified_cons (by exact certified1284)
  apply certified_cons (by exact certified1284swap)
  apply certified_cons (by exact certified1285)
  apply certified_cons (by exact certified1285swap)
  apply certified_cons (by exact certified1286)
  apply certified_cons (by exact certified1286swap)
  apply certified_cons (by exact certified1287)
  apply certified_cons (by exact certified1287swap)
  apply certified_cons (by exact certified1288)
  apply certified_cons (by exact certified1288swap)
  apply certified_cons (by exact certified1289)
  apply certified_cons (by exact certified1289swap)
  apply certified_cons (by exact certified1290)
  apply certified_cons (by exact certified1290swap)
  apply certified_cons (by exact certified1291)
  apply certified_cons (by exact certified1291swap)
  apply certified_cons (by exact certified1292)
  apply certified_cons (by exact certified1292swap)
  apply certified_cons (by exact certified1293)
  apply certified_cons (by exact certified1293swap)
  apply certified_cons (by exact certified1294)
  apply certified_cons (by exact certified1294swap)
  apply certified_cons (by exact certified1295)
  apply certified_cons (by exact certified1295swap)
  apply certified_cons (by exact certified1296)
  apply certified_cons (by exact certified1296swap)
  apply certified_cons (by exact certified1297)
  apply certified_cons (by exact certified1297swap)
  apply certified_cons (by exact certified1298)
  apply certified_cons (by exact certified1298swap)
  apply certified_cons (by exact certified1299)
  apply certified_cons (by exact certified1299swap)
  simp
#print axioms certified_keys025
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
