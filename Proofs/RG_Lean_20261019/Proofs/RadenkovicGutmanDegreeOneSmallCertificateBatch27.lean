/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1350
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1351
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1352
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1353
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1354
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1355
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1356
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1357
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1358
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1359
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1360
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1361
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1362
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1363
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1364
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1365
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1366
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1367
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1368
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1369
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1370
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1371
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1372
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1373
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1374
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1375
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1376
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1377
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1378
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1379
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1380
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1381
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1382
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1383
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1384
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1385
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1386
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1387
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1388
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1389
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1390
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1391
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1392
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1393
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1394
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1395
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1396
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1397
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1398
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1399
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys27 : ∀ k ∈ keys27, Certified k := by
  apply certified_cons (by exact certified1350)
  apply certified_cons (by exact certified1350swap)
  apply certified_cons (by exact certified1351)
  apply certified_cons (by exact certified1352)
  apply certified_cons (by exact certified1352swap)
  apply certified_cons (by exact certified1353)
  apply certified_cons (by exact certified1354)
  apply certified_cons (by exact certified1354swap)
  apply certified_cons (by exact certified1355)
  apply certified_cons (by exact certified1356)
  apply certified_cons (by exact certified1356swap)
  apply certified_cons (by exact certified1357)
  apply certified_cons (by exact certified1358)
  apply certified_cons (by exact certified1358swap)
  apply certified_cons (by exact certified1359)
  apply certified_cons (by exact certified1360)
  apply certified_cons (by exact certified1360swap)
  apply certified_cons (by exact certified1361)
  apply certified_cons (by exact certified1362)
  apply certified_cons (by exact certified1362swap)
  apply certified_cons (by exact certified1363)
  apply certified_cons (by exact certified1364)
  apply certified_cons (by exact certified1364swap)
  apply certified_cons (by exact certified1365)
  apply certified_cons (by exact certified1366)
  apply certified_cons (by exact certified1366swap)
  apply certified_cons (by exact certified1367)
  apply certified_cons (by exact certified1368)
  apply certified_cons (by exact certified1368swap)
  apply certified_cons (by exact certified1369)
  apply certified_cons (by exact certified1370)
  apply certified_cons (by exact certified1370swap)
  apply certified_cons (by exact certified1371)
  apply certified_cons (by exact certified1372)
  apply certified_cons (by exact certified1372swap)
  apply certified_cons (by exact certified1373)
  apply certified_cons (by exact certified1374)
  apply certified_cons (by exact certified1374swap)
  apply certified_cons (by exact certified1375)
  apply certified_cons (by exact certified1376)
  apply certified_cons (by exact certified1376swap)
  apply certified_cons (by exact certified1377)
  apply certified_cons (by exact certified1378)
  apply certified_cons (by exact certified1378swap)
  apply certified_cons (by exact certified1379)
  apply certified_cons (by exact certified1380)
  apply certified_cons (by exact certified1380swap)
  apply certified_cons (by exact certified1381)
  apply certified_cons (by exact certified1382)
  apply certified_cons (by exact certified1382swap)
  apply certified_cons (by exact certified1383)
  apply certified_cons (by exact certified1384)
  apply certified_cons (by exact certified1384swap)
  apply certified_cons (by exact certified1385)
  apply certified_cons (by exact certified1386)
  apply certified_cons (by exact certified1386swap)
  apply certified_cons (by exact certified1387)
  apply certified_cons (by exact certified1388)
  apply certified_cons (by exact certified1388swap)
  apply certified_cons (by exact certified1389)
  apply certified_cons (by exact certified1390)
  apply certified_cons (by exact certified1390swap)
  apply certified_cons (by exact certified1391)
  apply certified_cons (by exact certified1392)
  apply certified_cons (by exact certified1392swap)
  apply certified_cons (by exact certified1393)
  apply certified_cons (by exact certified1394)
  apply certified_cons (by exact certified1394swap)
  apply certified_cons (by exact certified1395)
  apply certified_cons (by exact certified1396)
  apply certified_cons (by exact certified1396swap)
  apply certified_cons (by exact certified1397)
  apply certified_cons (by exact certified1398)
  apply certified_cons (by exact certified1398swap)
  apply certified_cons (by exact certified1399)
  simp
#print axioms certified_keys27
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
