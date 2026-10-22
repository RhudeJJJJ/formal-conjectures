/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1350
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1351
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1352
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1353
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1354
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1355
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1356
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1357
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1358
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1359
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1360
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1361
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1362
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1363
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1364
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1365
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1366
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1367
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1368
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1369
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1370
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1371
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1372
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1373
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1374
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1375
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1376
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1377
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1378
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1379
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1380
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1381
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1382
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1383
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1384
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1385
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1386
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1387
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1388
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1389
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1390
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1391
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1392
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1393
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1394
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1395
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1396
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1397
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1398
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1399
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys027 : ∀ k ∈ keys027, Certified k := by
  apply certified_cons (by exact certified1350)
  apply certified_cons (by exact certified1350swap)
  apply certified_cons (by exact certified1351)
  apply certified_cons (by exact certified1351swap)
  apply certified_cons (by exact certified1352)
  apply certified_cons (by exact certified1352swap)
  apply certified_cons (by exact certified1353)
  apply certified_cons (by exact certified1353swap)
  apply certified_cons (by exact certified1354)
  apply certified_cons (by exact certified1354swap)
  apply certified_cons (by exact certified1355)
  apply certified_cons (by exact certified1355swap)
  apply certified_cons (by exact certified1356)
  apply certified_cons (by exact certified1356swap)
  apply certified_cons (by exact certified1357)
  apply certified_cons (by exact certified1357swap)
  apply certified_cons (by exact certified1358)
  apply certified_cons (by exact certified1358swap)
  apply certified_cons (by exact certified1359)
  apply certified_cons (by exact certified1359swap)
  apply certified_cons (by exact certified1360)
  apply certified_cons (by exact certified1360swap)
  apply certified_cons (by exact certified1361)
  apply certified_cons (by exact certified1361swap)
  apply certified_cons (by exact certified1362)
  apply certified_cons (by exact certified1362swap)
  apply certified_cons (by exact certified1363)
  apply certified_cons (by exact certified1363swap)
  apply certified_cons (by exact certified1364)
  apply certified_cons (by exact certified1364swap)
  apply certified_cons (by exact certified1365)
  apply certified_cons (by exact certified1365swap)
  apply certified_cons (by exact certified1366)
  apply certified_cons (by exact certified1366swap)
  apply certified_cons (by exact certified1367)
  apply certified_cons (by exact certified1367swap)
  apply certified_cons (by exact certified1368)
  apply certified_cons (by exact certified1368swap)
  apply certified_cons (by exact certified1369)
  apply certified_cons (by exact certified1369swap)
  apply certified_cons (by exact certified1370)
  apply certified_cons (by exact certified1370swap)
  apply certified_cons (by exact certified1371)
  apply certified_cons (by exact certified1371swap)
  apply certified_cons (by exact certified1372)
  apply certified_cons (by exact certified1372swap)
  apply certified_cons (by exact certified1373)
  apply certified_cons (by exact certified1373swap)
  apply certified_cons (by exact certified1374)
  apply certified_cons (by exact certified1374swap)
  apply certified_cons (by exact certified1375)
  apply certified_cons (by exact certified1375swap)
  apply certified_cons (by exact certified1376)
  apply certified_cons (by exact certified1376swap)
  apply certified_cons (by exact certified1377)
  apply certified_cons (by exact certified1377swap)
  apply certified_cons (by exact certified1378)
  apply certified_cons (by exact certified1378swap)
  apply certified_cons (by exact certified1379)
  apply certified_cons (by exact certified1379swap)
  apply certified_cons (by exact certified1380)
  apply certified_cons (by exact certified1380swap)
  apply certified_cons (by exact certified1381)
  apply certified_cons (by exact certified1381swap)
  apply certified_cons (by exact certified1382)
  apply certified_cons (by exact certified1382swap)
  apply certified_cons (by exact certified1383)
  apply certified_cons (by exact certified1383swap)
  apply certified_cons (by exact certified1384)
  apply certified_cons (by exact certified1384swap)
  apply certified_cons (by exact certified1385)
  apply certified_cons (by exact certified1385swap)
  apply certified_cons (by exact certified1386)
  apply certified_cons (by exact certified1386swap)
  apply certified_cons (by exact certified1387)
  apply certified_cons (by exact certified1387swap)
  apply certified_cons (by exact certified1388)
  apply certified_cons (by exact certified1388swap)
  apply certified_cons (by exact certified1389)
  apply certified_cons (by exact certified1389swap)
  apply certified_cons (by exact certified1390)
  apply certified_cons (by exact certified1390swap)
  apply certified_cons (by exact certified1391)
  apply certified_cons (by exact certified1391swap)
  apply certified_cons (by exact certified1392)
  apply certified_cons (by exact certified1392swap)
  apply certified_cons (by exact certified1393)
  apply certified_cons (by exact certified1393swap)
  apply certified_cons (by exact certified1394)
  apply certified_cons (by exact certified1394swap)
  apply certified_cons (by exact certified1395)
  apply certified_cons (by exact certified1395swap)
  apply certified_cons (by exact certified1396)
  apply certified_cons (by exact certified1396swap)
  apply certified_cons (by exact certified1397)
  apply certified_cons (by exact certified1397swap)
  apply certified_cons (by exact certified1398)
  apply certified_cons (by exact certified1398swap)
  apply certified_cons (by exact certified1399)
  apply certified_cons (by exact certified1399swap)
  simp
#print axioms certified_keys027
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
