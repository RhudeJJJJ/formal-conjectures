/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1400
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1401
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1402
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1403
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1404
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1405
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1406
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1407
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1408
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1409
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1410
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1411
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1412
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1413
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1414
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1415
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1416
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1417
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1418
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1419
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1420
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1421
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1422
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1423
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1424
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1425
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1426
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1427
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1428
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1429
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1430
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1431
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1432
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1433
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1434
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1435
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1436
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1437
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1438
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1439
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1440
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1441
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1442
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1443
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1444
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1445
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1446
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1447
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1448
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1449
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys28 : ∀ k ∈ keys28, Certified k := by
  apply certified_cons (by exact certified1400)
  apply certified_cons (by exact certified1400swap)
  apply certified_cons (by exact certified1401)
  apply certified_cons (by exact certified1402)
  apply certified_cons (by exact certified1402swap)
  apply certified_cons (by exact certified1403)
  apply certified_cons (by exact certified1404)
  apply certified_cons (by exact certified1404swap)
  apply certified_cons (by exact certified1405)
  apply certified_cons (by exact certified1406)
  apply certified_cons (by exact certified1406swap)
  apply certified_cons (by exact certified1407)
  apply certified_cons (by exact certified1408)
  apply certified_cons (by exact certified1408swap)
  apply certified_cons (by exact certified1409)
  apply certified_cons (by exact certified1410)
  apply certified_cons (by exact certified1410swap)
  apply certified_cons (by exact certified1411)
  apply certified_cons (by exact certified1412)
  apply certified_cons (by exact certified1412swap)
  apply certified_cons (by exact certified1413)
  apply certified_cons (by exact certified1414)
  apply certified_cons (by exact certified1414swap)
  apply certified_cons (by exact certified1415)
  apply certified_cons (by exact certified1416)
  apply certified_cons (by exact certified1416swap)
  apply certified_cons (by exact certified1417)
  apply certified_cons (by exact certified1418)
  apply certified_cons (by exact certified1418swap)
  apply certified_cons (by exact certified1419)
  apply certified_cons (by exact certified1420)
  apply certified_cons (by exact certified1420swap)
  apply certified_cons (by exact certified1421)
  apply certified_cons (by exact certified1422)
  apply certified_cons (by exact certified1422swap)
  apply certified_cons (by exact certified1423)
  apply certified_cons (by exact certified1424)
  apply certified_cons (by exact certified1424swap)
  apply certified_cons (by exact certified1425)
  apply certified_cons (by exact certified1426)
  apply certified_cons (by exact certified1426swap)
  apply certified_cons (by exact certified1427)
  apply certified_cons (by exact certified1428)
  apply certified_cons (by exact certified1428swap)
  apply certified_cons (by exact certified1429)
  apply certified_cons (by exact certified1430)
  apply certified_cons (by exact certified1430swap)
  apply certified_cons (by exact certified1431)
  apply certified_cons (by exact certified1432)
  apply certified_cons (by exact certified1432swap)
  apply certified_cons (by exact certified1433)
  apply certified_cons (by exact certified1434)
  apply certified_cons (by exact certified1434swap)
  apply certified_cons (by exact certified1435)
  apply certified_cons (by exact certified1436)
  apply certified_cons (by exact certified1436swap)
  apply certified_cons (by exact certified1437)
  apply certified_cons (by exact certified1438)
  apply certified_cons (by exact certified1438swap)
  apply certified_cons (by exact certified1439)
  apply certified_cons (by exact certified1440)
  apply certified_cons (by exact certified1440swap)
  apply certified_cons (by exact certified1441)
  apply certified_cons (by exact certified1442)
  apply certified_cons (by exact certified1442swap)
  apply certified_cons (by exact certified1443)
  apply certified_cons (by exact certified1444)
  apply certified_cons (by exact certified1444swap)
  apply certified_cons (by exact certified1445)
  apply certified_cons (by exact certified1446)
  apply certified_cons (by exact certified1446swap)
  apply certified_cons (by exact certified1447)
  apply certified_cons (by exact certified1448)
  apply certified_cons (by exact certified1448swap)
  apply certified_cons (by exact certified1449)
  simp
#print axioms certified_keys28
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
