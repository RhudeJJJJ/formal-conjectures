/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1400
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1401
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1402
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1403
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1404
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1405
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1406
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1407
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1408
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1409
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1410
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1411
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1412
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1413
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1414
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1415
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1416
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1417
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1418
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1419
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1420
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1421
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1422
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1423
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1424
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1425
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1426
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1427
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1428
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1429
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1430
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1431
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1432
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1433
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1434
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1435
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1436
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1437
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1438
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1439
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1440
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1441
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1442
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1443
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1444
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1445
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1446
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1447
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1448
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1449
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys028 : ∀ k ∈ keys028, Certified k := by
  apply certified_cons (by exact certified1400)
  apply certified_cons (by exact certified1400swap)
  apply certified_cons (by exact certified1401)
  apply certified_cons (by exact certified1401swap)
  apply certified_cons (by exact certified1402)
  apply certified_cons (by exact certified1402swap)
  apply certified_cons (by exact certified1403)
  apply certified_cons (by exact certified1403swap)
  apply certified_cons (by exact certified1404)
  apply certified_cons (by exact certified1404swap)
  apply certified_cons (by exact certified1405)
  apply certified_cons (by exact certified1405swap)
  apply certified_cons (by exact certified1406)
  apply certified_cons (by exact certified1406swap)
  apply certified_cons (by exact certified1407)
  apply certified_cons (by exact certified1407swap)
  apply certified_cons (by exact certified1408)
  apply certified_cons (by exact certified1408swap)
  apply certified_cons (by exact certified1409)
  apply certified_cons (by exact certified1409swap)
  apply certified_cons (by exact certified1410)
  apply certified_cons (by exact certified1410swap)
  apply certified_cons (by exact certified1411)
  apply certified_cons (by exact certified1411swap)
  apply certified_cons (by exact certified1412)
  apply certified_cons (by exact certified1412swap)
  apply certified_cons (by exact certified1413)
  apply certified_cons (by exact certified1413swap)
  apply certified_cons (by exact certified1414)
  apply certified_cons (by exact certified1414swap)
  apply certified_cons (by exact certified1415)
  apply certified_cons (by exact certified1415swap)
  apply certified_cons (by exact certified1416)
  apply certified_cons (by exact certified1416swap)
  apply certified_cons (by exact certified1417)
  apply certified_cons (by exact certified1417swap)
  apply certified_cons (by exact certified1418)
  apply certified_cons (by exact certified1418swap)
  apply certified_cons (by exact certified1419)
  apply certified_cons (by exact certified1419swap)
  apply certified_cons (by exact certified1420)
  apply certified_cons (by exact certified1420swap)
  apply certified_cons (by exact certified1421)
  apply certified_cons (by exact certified1421swap)
  apply certified_cons (by exact certified1422)
  apply certified_cons (by exact certified1422swap)
  apply certified_cons (by exact certified1423)
  apply certified_cons (by exact certified1423swap)
  apply certified_cons (by exact certified1424)
  apply certified_cons (by exact certified1424swap)
  apply certified_cons (by exact certified1425)
  apply certified_cons (by exact certified1425swap)
  apply certified_cons (by exact certified1426)
  apply certified_cons (by exact certified1426swap)
  apply certified_cons (by exact certified1427)
  apply certified_cons (by exact certified1427swap)
  apply certified_cons (by exact certified1428)
  apply certified_cons (by exact certified1428swap)
  apply certified_cons (by exact certified1429)
  apply certified_cons (by exact certified1429swap)
  apply certified_cons (by exact certified1430)
  apply certified_cons (by exact certified1430swap)
  apply certified_cons (by exact certified1431)
  apply certified_cons (by exact certified1431swap)
  apply certified_cons (by exact certified1432)
  apply certified_cons (by exact certified1432swap)
  apply certified_cons (by exact certified1433)
  apply certified_cons (by exact certified1433swap)
  apply certified_cons (by exact certified1434)
  apply certified_cons (by exact certified1434swap)
  apply certified_cons (by exact certified1435)
  apply certified_cons (by exact certified1435swap)
  apply certified_cons (by exact certified1436)
  apply certified_cons (by exact certified1436swap)
  apply certified_cons (by exact certified1437)
  apply certified_cons (by exact certified1437swap)
  apply certified_cons (by exact certified1438)
  apply certified_cons (by exact certified1438swap)
  apply certified_cons (by exact certified1439)
  apply certified_cons (by exact certified1439swap)
  apply certified_cons (by exact certified1440)
  apply certified_cons (by exact certified1440swap)
  apply certified_cons (by exact certified1441)
  apply certified_cons (by exact certified1441swap)
  apply certified_cons (by exact certified1442)
  apply certified_cons (by exact certified1442swap)
  apply certified_cons (by exact certified1443)
  apply certified_cons (by exact certified1443swap)
  apply certified_cons (by exact certified1444)
  apply certified_cons (by exact certified1444swap)
  apply certified_cons (by exact certified1445)
  apply certified_cons (by exact certified1445swap)
  apply certified_cons (by exact certified1446)
  apply certified_cons (by exact certified1446swap)
  apply certified_cons (by exact certified1447)
  apply certified_cons (by exact certified1447swap)
  apply certified_cons (by exact certified1448)
  apply certified_cons (by exact certified1448swap)
  apply certified_cons (by exact certified1449)
  apply certified_cons (by exact certified1449swap)
  simp
#print axioms certified_keys028
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
