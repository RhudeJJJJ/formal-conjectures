/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1300
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1301
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1302
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1303
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1304
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1305
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1306
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1307
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1308
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1309
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1310
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1311
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1312
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1313
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1314
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1315
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1316
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1317
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1318
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1319
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1320
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1321
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1322
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1323
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1324
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1325
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1326
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1327
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1328
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1329
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1330
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1331
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1332
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1333
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1334
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1335
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1336
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1337
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1338
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1339
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1340
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1341
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1342
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1343
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1344
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1345
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1346
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1347
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1348
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1349
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys026 : ∀ k ∈ keys026, Certified k := by
  apply certified_cons (by exact certified1300)
  apply certified_cons (by exact certified1300swap)
  apply certified_cons (by exact certified1301)
  apply certified_cons (by exact certified1301swap)
  apply certified_cons (by exact certified1302)
  apply certified_cons (by exact certified1302swap)
  apply certified_cons (by exact certified1303)
  apply certified_cons (by exact certified1303swap)
  apply certified_cons (by exact certified1304)
  apply certified_cons (by exact certified1304swap)
  apply certified_cons (by exact certified1305)
  apply certified_cons (by exact certified1305swap)
  apply certified_cons (by exact certified1306)
  apply certified_cons (by exact certified1306swap)
  apply certified_cons (by exact certified1307)
  apply certified_cons (by exact certified1307swap)
  apply certified_cons (by exact certified1308)
  apply certified_cons (by exact certified1308swap)
  apply certified_cons (by exact certified1309)
  apply certified_cons (by exact certified1309swap)
  apply certified_cons (by exact certified1310)
  apply certified_cons (by exact certified1310swap)
  apply certified_cons (by exact certified1311)
  apply certified_cons (by exact certified1311swap)
  apply certified_cons (by exact certified1312)
  apply certified_cons (by exact certified1312swap)
  apply certified_cons (by exact certified1313)
  apply certified_cons (by exact certified1313swap)
  apply certified_cons (by exact certified1314)
  apply certified_cons (by exact certified1314swap)
  apply certified_cons (by exact certified1315)
  apply certified_cons (by exact certified1315swap)
  apply certified_cons (by exact certified1316)
  apply certified_cons (by exact certified1316swap)
  apply certified_cons (by exact certified1317)
  apply certified_cons (by exact certified1317swap)
  apply certified_cons (by exact certified1318)
  apply certified_cons (by exact certified1318swap)
  apply certified_cons (by exact certified1319)
  apply certified_cons (by exact certified1319swap)
  apply certified_cons (by exact certified1320)
  apply certified_cons (by exact certified1320swap)
  apply certified_cons (by exact certified1321)
  apply certified_cons (by exact certified1321swap)
  apply certified_cons (by exact certified1322)
  apply certified_cons (by exact certified1322swap)
  apply certified_cons (by exact certified1323)
  apply certified_cons (by exact certified1323swap)
  apply certified_cons (by exact certified1324)
  apply certified_cons (by exact certified1324swap)
  apply certified_cons (by exact certified1325)
  apply certified_cons (by exact certified1325swap)
  apply certified_cons (by exact certified1326)
  apply certified_cons (by exact certified1326swap)
  apply certified_cons (by exact certified1327)
  apply certified_cons (by exact certified1327swap)
  apply certified_cons (by exact certified1328)
  apply certified_cons (by exact certified1328swap)
  apply certified_cons (by exact certified1329)
  apply certified_cons (by exact certified1329swap)
  apply certified_cons (by exact certified1330)
  apply certified_cons (by exact certified1330swap)
  apply certified_cons (by exact certified1331)
  apply certified_cons (by exact certified1331swap)
  apply certified_cons (by exact certified1332)
  apply certified_cons (by exact certified1332swap)
  apply certified_cons (by exact certified1333)
  apply certified_cons (by exact certified1333swap)
  apply certified_cons (by exact certified1334)
  apply certified_cons (by exact certified1334swap)
  apply certified_cons (by exact certified1335)
  apply certified_cons (by exact certified1335swap)
  apply certified_cons (by exact certified1336)
  apply certified_cons (by exact certified1336swap)
  apply certified_cons (by exact certified1337)
  apply certified_cons (by exact certified1337swap)
  apply certified_cons (by exact certified1338)
  apply certified_cons (by exact certified1338swap)
  apply certified_cons (by exact certified1339)
  apply certified_cons (by exact certified1339swap)
  apply certified_cons (by exact certified1340)
  apply certified_cons (by exact certified1340swap)
  apply certified_cons (by exact certified1341)
  apply certified_cons (by exact certified1341swap)
  apply certified_cons (by exact certified1342)
  apply certified_cons (by exact certified1342swap)
  apply certified_cons (by exact certified1343)
  apply certified_cons (by exact certified1343swap)
  apply certified_cons (by exact certified1344)
  apply certified_cons (by exact certified1344swap)
  apply certified_cons (by exact certified1345)
  apply certified_cons (by exact certified1345swap)
  apply certified_cons (by exact certified1346)
  apply certified_cons (by exact certified1346swap)
  apply certified_cons (by exact certified1347)
  apply certified_cons (by exact certified1347swap)
  apply certified_cons (by exact certified1348)
  apply certified_cons (by exact certified1348swap)
  apply certified_cons (by exact certified1349)
  apply certified_cons (by exact certified1349swap)
  simp
#print axioms certified_keys026
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
