/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1450
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1451
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1452
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1453
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1454
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1455
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1456
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1457
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1458
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1459
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1460
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1461
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1462
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1463
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1464
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1465
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1466
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1467
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1468
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1469
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1470
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1471
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1472
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1473
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1474
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1475
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1476
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1477
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1478
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1479
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1480
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1481
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1482
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1483
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1484
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1485
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1486
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1487
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1488
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1489
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1490
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1491
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1492
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1493
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1494
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1495
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1496
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1497
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1498
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1499
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys029 : ∀ k ∈ keys029, Certified k := by
  apply certified_cons (by exact certified1450)
  apply certified_cons (by exact certified1450swap)
  apply certified_cons (by exact certified1451)
  apply certified_cons (by exact certified1451swap)
  apply certified_cons (by exact certified1452)
  apply certified_cons (by exact certified1452swap)
  apply certified_cons (by exact certified1453)
  apply certified_cons (by exact certified1453swap)
  apply certified_cons (by exact certified1454)
  apply certified_cons (by exact certified1454swap)
  apply certified_cons (by exact certified1455)
  apply certified_cons (by exact certified1455swap)
  apply certified_cons (by exact certified1456)
  apply certified_cons (by exact certified1456swap)
  apply certified_cons (by exact certified1457)
  apply certified_cons (by exact certified1457swap)
  apply certified_cons (by exact certified1458)
  apply certified_cons (by exact certified1458swap)
  apply certified_cons (by exact certified1459)
  apply certified_cons (by exact certified1459swap)
  apply certified_cons (by exact certified1460)
  apply certified_cons (by exact certified1460swap)
  apply certified_cons (by exact certified1461)
  apply certified_cons (by exact certified1461swap)
  apply certified_cons (by exact certified1462)
  apply certified_cons (by exact certified1462swap)
  apply certified_cons (by exact certified1463)
  apply certified_cons (by exact certified1463swap)
  apply certified_cons (by exact certified1464)
  apply certified_cons (by exact certified1464swap)
  apply certified_cons (by exact certified1465)
  apply certified_cons (by exact certified1465swap)
  apply certified_cons (by exact certified1466)
  apply certified_cons (by exact certified1466swap)
  apply certified_cons (by exact certified1467)
  apply certified_cons (by exact certified1467swap)
  apply certified_cons (by exact certified1468)
  apply certified_cons (by exact certified1468swap)
  apply certified_cons (by exact certified1469)
  apply certified_cons (by exact certified1469swap)
  apply certified_cons (by exact certified1470)
  apply certified_cons (by exact certified1470swap)
  apply certified_cons (by exact certified1471)
  apply certified_cons (by exact certified1471swap)
  apply certified_cons (by exact certified1472)
  apply certified_cons (by exact certified1472swap)
  apply certified_cons (by exact certified1473)
  apply certified_cons (by exact certified1473swap)
  apply certified_cons (by exact certified1474)
  apply certified_cons (by exact certified1474swap)
  apply certified_cons (by exact certified1475)
  apply certified_cons (by exact certified1475swap)
  apply certified_cons (by exact certified1476)
  apply certified_cons (by exact certified1476swap)
  apply certified_cons (by exact certified1477)
  apply certified_cons (by exact certified1477swap)
  apply certified_cons (by exact certified1478)
  apply certified_cons (by exact certified1478swap)
  apply certified_cons (by exact certified1479)
  apply certified_cons (by exact certified1479swap)
  apply certified_cons (by exact certified1480)
  apply certified_cons (by exact certified1480swap)
  apply certified_cons (by exact certified1481)
  apply certified_cons (by exact certified1481swap)
  apply certified_cons (by exact certified1482)
  apply certified_cons (by exact certified1482swap)
  apply certified_cons (by exact certified1483)
  apply certified_cons (by exact certified1483swap)
  apply certified_cons (by exact certified1484)
  apply certified_cons (by exact certified1484swap)
  apply certified_cons (by exact certified1485)
  apply certified_cons (by exact certified1485swap)
  apply certified_cons (by exact certified1486)
  apply certified_cons (by exact certified1486swap)
  apply certified_cons (by exact certified1487)
  apply certified_cons (by exact certified1487swap)
  apply certified_cons (by exact certified1488)
  apply certified_cons (by exact certified1488swap)
  apply certified_cons (by exact certified1489)
  apply certified_cons (by exact certified1489swap)
  apply certified_cons (by exact certified1490)
  apply certified_cons (by exact certified1490swap)
  apply certified_cons (by exact certified1491)
  apply certified_cons (by exact certified1491swap)
  apply certified_cons (by exact certified1492)
  apply certified_cons (by exact certified1492swap)
  apply certified_cons (by exact certified1493)
  apply certified_cons (by exact certified1493swap)
  apply certified_cons (by exact certified1494)
  apply certified_cons (by exact certified1494swap)
  apply certified_cons (by exact certified1495)
  apply certified_cons (by exact certified1495swap)
  apply certified_cons (by exact certified1496)
  apply certified_cons (by exact certified1496swap)
  apply certified_cons (by exact certified1497)
  apply certified_cons (by exact certified1497swap)
  apply certified_cons (by exact certified1498)
  apply certified_cons (by exact certified1498swap)
  apply certified_cons (by exact certified1499)
  apply certified_cons (by exact certified1499swap)
  simp
#print axioms certified_keys029
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
