/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1300
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1301
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1302
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1303
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1304
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1305
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1306
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1307
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1308
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1309
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1310
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1311
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1312
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1313
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1314
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1315
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1316
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1317
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1318
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1319
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1320
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1321
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1322
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1323
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1324
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1325
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1326
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1327
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1328
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1329
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1330
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1331
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1332
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1333
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1334
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1335
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1336
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1337
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1338
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1339
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1340
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1341
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1342
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1343
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1344
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1345
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1346
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1347
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1348
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1349
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys26 : ∀ k ∈ keys26, Certified k := by
  apply certified_cons (by exact certified1300)
  apply certified_cons (by exact certified1300swap)
  apply certified_cons (by exact certified1301)
  apply certified_cons (by exact certified1302)
  apply certified_cons (by exact certified1302swap)
  apply certified_cons (by exact certified1303)
  apply certified_cons (by exact certified1304)
  apply certified_cons (by exact certified1304swap)
  apply certified_cons (by exact certified1305)
  apply certified_cons (by exact certified1306)
  apply certified_cons (by exact certified1306swap)
  apply certified_cons (by exact certified1307)
  apply certified_cons (by exact certified1308)
  apply certified_cons (by exact certified1308swap)
  apply certified_cons (by exact certified1309)
  apply certified_cons (by exact certified1310)
  apply certified_cons (by exact certified1310swap)
  apply certified_cons (by exact certified1311)
  apply certified_cons (by exact certified1312)
  apply certified_cons (by exact certified1312swap)
  apply certified_cons (by exact certified1313)
  apply certified_cons (by exact certified1314)
  apply certified_cons (by exact certified1314swap)
  apply certified_cons (by exact certified1315)
  apply certified_cons (by exact certified1316)
  apply certified_cons (by exact certified1316swap)
  apply certified_cons (by exact certified1317)
  apply certified_cons (by exact certified1318)
  apply certified_cons (by exact certified1318swap)
  apply certified_cons (by exact certified1319)
  apply certified_cons (by exact certified1320)
  apply certified_cons (by exact certified1320swap)
  apply certified_cons (by exact certified1321)
  apply certified_cons (by exact certified1322)
  apply certified_cons (by exact certified1322swap)
  apply certified_cons (by exact certified1323)
  apply certified_cons (by exact certified1324)
  apply certified_cons (by exact certified1324swap)
  apply certified_cons (by exact certified1325)
  apply certified_cons (by exact certified1326)
  apply certified_cons (by exact certified1326swap)
  apply certified_cons (by exact certified1327)
  apply certified_cons (by exact certified1328)
  apply certified_cons (by exact certified1328swap)
  apply certified_cons (by exact certified1329)
  apply certified_cons (by exact certified1330)
  apply certified_cons (by exact certified1330swap)
  apply certified_cons (by exact certified1331)
  apply certified_cons (by exact certified1332)
  apply certified_cons (by exact certified1332swap)
  apply certified_cons (by exact certified1333)
  apply certified_cons (by exact certified1334)
  apply certified_cons (by exact certified1334swap)
  apply certified_cons (by exact certified1335)
  apply certified_cons (by exact certified1336)
  apply certified_cons (by exact certified1336swap)
  apply certified_cons (by exact certified1337)
  apply certified_cons (by exact certified1338)
  apply certified_cons (by exact certified1338swap)
  apply certified_cons (by exact certified1339)
  apply certified_cons (by exact certified1340)
  apply certified_cons (by exact certified1340swap)
  apply certified_cons (by exact certified1341)
  apply certified_cons (by exact certified1342)
  apply certified_cons (by exact certified1342swap)
  apply certified_cons (by exact certified1343)
  apply certified_cons (by exact certified1344)
  apply certified_cons (by exact certified1344swap)
  apply certified_cons (by exact certified1345)
  apply certified_cons (by exact certified1346)
  apply certified_cons (by exact certified1346swap)
  apply certified_cons (by exact certified1347)
  apply certified_cons (by exact certified1348)
  apply certified_cons (by exact certified1348swap)
  apply certified_cons (by exact certified1349)
  simp
#print axioms certified_keys26
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
