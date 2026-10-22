/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1500
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1501
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1502
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1503
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1504
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1505
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1506
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1507
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1508
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1509
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1510
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1511
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1512
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1513
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1514
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1515
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1516
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1517
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1518
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1519
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1520
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1521
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1522
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1523
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1524
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1525
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1526
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1527
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1528
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1529
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1530
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1531
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1532
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1533
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1534
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1535
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1536
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1537
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1538
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1539
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1540
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1541
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1542
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1543
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1544
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1545
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1546
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1547
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1548
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1549
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys030 : ∀ k ∈ keys030, Certified k := by
  apply certified_cons (by exact certified1500)
  apply certified_cons (by exact certified1500swap)
  apply certified_cons (by exact certified1501)
  apply certified_cons (by exact certified1501swap)
  apply certified_cons (by exact certified1502)
  apply certified_cons (by exact certified1502swap)
  apply certified_cons (by exact certified1503)
  apply certified_cons (by exact certified1503swap)
  apply certified_cons (by exact certified1504)
  apply certified_cons (by exact certified1504swap)
  apply certified_cons (by exact certified1505)
  apply certified_cons (by exact certified1505swap)
  apply certified_cons (by exact certified1506)
  apply certified_cons (by exact certified1506swap)
  apply certified_cons (by exact certified1507)
  apply certified_cons (by exact certified1507swap)
  apply certified_cons (by exact certified1508)
  apply certified_cons (by exact certified1508swap)
  apply certified_cons (by exact certified1509)
  apply certified_cons (by exact certified1509swap)
  apply certified_cons (by exact certified1510)
  apply certified_cons (by exact certified1510swap)
  apply certified_cons (by exact certified1511)
  apply certified_cons (by exact certified1511swap)
  apply certified_cons (by exact certified1512)
  apply certified_cons (by exact certified1512swap)
  apply certified_cons (by exact certified1513)
  apply certified_cons (by exact certified1513swap)
  apply certified_cons (by exact certified1514)
  apply certified_cons (by exact certified1514swap)
  apply certified_cons (by exact certified1515)
  apply certified_cons (by exact certified1515swap)
  apply certified_cons (by exact certified1516)
  apply certified_cons (by exact certified1516swap)
  apply certified_cons (by exact certified1517)
  apply certified_cons (by exact certified1517swap)
  apply certified_cons (by exact certified1518)
  apply certified_cons (by exact certified1518swap)
  apply certified_cons (by exact certified1519)
  apply certified_cons (by exact certified1519swap)
  apply certified_cons (by exact certified1520)
  apply certified_cons (by exact certified1520swap)
  apply certified_cons (by exact certified1521)
  apply certified_cons (by exact certified1521swap)
  apply certified_cons (by exact certified1522)
  apply certified_cons (by exact certified1522swap)
  apply certified_cons (by exact certified1523)
  apply certified_cons (by exact certified1523swap)
  apply certified_cons (by exact certified1524)
  apply certified_cons (by exact certified1524swap)
  apply certified_cons (by exact certified1525)
  apply certified_cons (by exact certified1525swap)
  apply certified_cons (by exact certified1526)
  apply certified_cons (by exact certified1526swap)
  apply certified_cons (by exact certified1527)
  apply certified_cons (by exact certified1527swap)
  apply certified_cons (by exact certified1528)
  apply certified_cons (by exact certified1528swap)
  apply certified_cons (by exact certified1529)
  apply certified_cons (by exact certified1529swap)
  apply certified_cons (by exact certified1530)
  apply certified_cons (by exact certified1530swap)
  apply certified_cons (by exact certified1531)
  apply certified_cons (by exact certified1531swap)
  apply certified_cons (by exact certified1532)
  apply certified_cons (by exact certified1532swap)
  apply certified_cons (by exact certified1533)
  apply certified_cons (by exact certified1533swap)
  apply certified_cons (by exact certified1534)
  apply certified_cons (by exact certified1534swap)
  apply certified_cons (by exact certified1535)
  apply certified_cons (by exact certified1535swap)
  apply certified_cons (by exact certified1536)
  apply certified_cons (by exact certified1536swap)
  apply certified_cons (by exact certified1537)
  apply certified_cons (by exact certified1537swap)
  apply certified_cons (by exact certified1538)
  apply certified_cons (by exact certified1538swap)
  apply certified_cons (by exact certified1539)
  apply certified_cons (by exact certified1539swap)
  apply certified_cons (by exact certified1540)
  apply certified_cons (by exact certified1540swap)
  apply certified_cons (by exact certified1541)
  apply certified_cons (by exact certified1541swap)
  apply certified_cons (by exact certified1542)
  apply certified_cons (by exact certified1542swap)
  apply certified_cons (by exact certified1543)
  apply certified_cons (by exact certified1543swap)
  apply certified_cons (by exact certified1544)
  apply certified_cons (by exact certified1544swap)
  apply certified_cons (by exact certified1545)
  apply certified_cons (by exact certified1545swap)
  apply certified_cons (by exact certified1546)
  apply certified_cons (by exact certified1546swap)
  apply certified_cons (by exact certified1547)
  apply certified_cons (by exact certified1547swap)
  apply certified_cons (by exact certified1548)
  apply certified_cons (by exact certified1548swap)
  apply certified_cons (by exact certified1549)
  apply certified_cons (by exact certified1549swap)
  simp
#print axioms certified_keys030
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
