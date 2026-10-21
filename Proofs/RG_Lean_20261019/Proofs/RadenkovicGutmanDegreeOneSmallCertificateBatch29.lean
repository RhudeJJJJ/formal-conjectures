/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1450
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1451
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1452
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1453
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1454
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1455
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1456
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1457
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1458
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1459
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1460
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1461
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1462
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1463
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1464
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1465
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1466
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1467
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1468
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1469
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1470
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1471
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1472
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1473
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1474
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1475
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1476
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1477
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1478
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1479
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1480
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1481
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1482
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1483
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1484
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1485
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1486
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1487
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1488
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1489
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1490
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1491
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1492
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1493
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1494
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1495
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1496
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1497
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1498
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1499
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys29 : ∀ k ∈ keys29, Certified k := by
  apply certified_cons (by exact certified1450)
  apply certified_cons (by exact certified1450swap)
  apply certified_cons (by exact certified1451)
  apply certified_cons (by exact certified1452)
  apply certified_cons (by exact certified1452swap)
  apply certified_cons (by exact certified1453)
  apply certified_cons (by exact certified1454)
  apply certified_cons (by exact certified1454swap)
  apply certified_cons (by exact certified1455)
  apply certified_cons (by exact certified1456)
  apply certified_cons (by exact certified1456swap)
  apply certified_cons (by exact certified1457)
  apply certified_cons (by exact certified1458)
  apply certified_cons (by exact certified1458swap)
  apply certified_cons (by exact certified1459)
  apply certified_cons (by exact certified1460)
  apply certified_cons (by exact certified1460swap)
  apply certified_cons (by exact certified1461)
  apply certified_cons (by exact certified1462)
  apply certified_cons (by exact certified1462swap)
  apply certified_cons (by exact certified1463)
  apply certified_cons (by exact certified1464)
  apply certified_cons (by exact certified1464swap)
  apply certified_cons (by exact certified1465)
  apply certified_cons (by exact certified1466)
  apply certified_cons (by exact certified1466swap)
  apply certified_cons (by exact certified1467)
  apply certified_cons (by exact certified1468)
  apply certified_cons (by exact certified1468swap)
  apply certified_cons (by exact certified1469)
  apply certified_cons (by exact certified1470)
  apply certified_cons (by exact certified1470swap)
  apply certified_cons (by exact certified1471)
  apply certified_cons (by exact certified1472)
  apply certified_cons (by exact certified1472swap)
  apply certified_cons (by exact certified1473)
  apply certified_cons (by exact certified1474)
  apply certified_cons (by exact certified1474swap)
  apply certified_cons (by exact certified1475)
  apply certified_cons (by exact certified1476)
  apply certified_cons (by exact certified1476swap)
  apply certified_cons (by exact certified1477)
  apply certified_cons (by exact certified1478)
  apply certified_cons (by exact certified1478swap)
  apply certified_cons (by exact certified1479)
  apply certified_cons (by exact certified1480)
  apply certified_cons (by exact certified1480swap)
  apply certified_cons (by exact certified1481)
  apply certified_cons (by exact certified1482)
  apply certified_cons (by exact certified1482swap)
  apply certified_cons (by exact certified1483)
  apply certified_cons (by exact certified1484)
  apply certified_cons (by exact certified1484swap)
  apply certified_cons (by exact certified1485)
  apply certified_cons (by exact certified1486)
  apply certified_cons (by exact certified1486swap)
  apply certified_cons (by exact certified1487)
  apply certified_cons (by exact certified1488)
  apply certified_cons (by exact certified1488swap)
  apply certified_cons (by exact certified1489)
  apply certified_cons (by exact certified1490)
  apply certified_cons (by exact certified1490swap)
  apply certified_cons (by exact certified1491)
  apply certified_cons (by exact certified1492)
  apply certified_cons (by exact certified1492swap)
  apply certified_cons (by exact certified1493)
  apply certified_cons (by exact certified1494)
  apply certified_cons (by exact certified1494swap)
  apply certified_cons (by exact certified1495)
  apply certified_cons (by exact certified1496)
  apply certified_cons (by exact certified1496swap)
  apply certified_cons (by exact certified1497)
  apply certified_cons (by exact certified1498)
  apply certified_cons (by exact certified1498swap)
  apply certified_cons (by exact certified1499)
  simp
#print axioms certified_keys29
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
