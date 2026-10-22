/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1550
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1551
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1552
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1553
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1554
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1555
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1556
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1557
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1558
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1559
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1560
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1561
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1562
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1563
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1564
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1565
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1566
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1567
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1568
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1569
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1570
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1571
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1572
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1573
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1574
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1575
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1576
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1577
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1578
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1579
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1580
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1581
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1582
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1583
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1584
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1585
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1586
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1587
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1588
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1589
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1590
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1591
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1592
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1593
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1594
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1595
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1596
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1597
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1598
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1599
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys031 : ∀ k ∈ keys031, Certified k := by
  apply certified_cons (by exact certified1550)
  apply certified_cons (by exact certified1550swap)
  apply certified_cons (by exact certified1551)
  apply certified_cons (by exact certified1551swap)
  apply certified_cons (by exact certified1552)
  apply certified_cons (by exact certified1552swap)
  apply certified_cons (by exact certified1553)
  apply certified_cons (by exact certified1553swap)
  apply certified_cons (by exact certified1554)
  apply certified_cons (by exact certified1554swap)
  apply certified_cons (by exact certified1555)
  apply certified_cons (by exact certified1555swap)
  apply certified_cons (by exact certified1556)
  apply certified_cons (by exact certified1556swap)
  apply certified_cons (by exact certified1557)
  apply certified_cons (by exact certified1557swap)
  apply certified_cons (by exact certified1558)
  apply certified_cons (by exact certified1558swap)
  apply certified_cons (by exact certified1559)
  apply certified_cons (by exact certified1559swap)
  apply certified_cons (by exact certified1560)
  apply certified_cons (by exact certified1560swap)
  apply certified_cons (by exact certified1561)
  apply certified_cons (by exact certified1561swap)
  apply certified_cons (by exact certified1562)
  apply certified_cons (by exact certified1562swap)
  apply certified_cons (by exact certified1563)
  apply certified_cons (by exact certified1563swap)
  apply certified_cons (by exact certified1564)
  apply certified_cons (by exact certified1564swap)
  apply certified_cons (by exact certified1565)
  apply certified_cons (by exact certified1565swap)
  apply certified_cons (by exact certified1566)
  apply certified_cons (by exact certified1566swap)
  apply certified_cons (by exact certified1567)
  apply certified_cons (by exact certified1567swap)
  apply certified_cons (by exact certified1568)
  apply certified_cons (by exact certified1568swap)
  apply certified_cons (by exact certified1569)
  apply certified_cons (by exact certified1569swap)
  apply certified_cons (by exact certified1570)
  apply certified_cons (by exact certified1570swap)
  apply certified_cons (by exact certified1571)
  apply certified_cons (by exact certified1571swap)
  apply certified_cons (by exact certified1572)
  apply certified_cons (by exact certified1572swap)
  apply certified_cons (by exact certified1573)
  apply certified_cons (by exact certified1573swap)
  apply certified_cons (by exact certified1574)
  apply certified_cons (by exact certified1574swap)
  apply certified_cons (by exact certified1575)
  apply certified_cons (by exact certified1575swap)
  apply certified_cons (by exact certified1576)
  apply certified_cons (by exact certified1576swap)
  apply certified_cons (by exact certified1577)
  apply certified_cons (by exact certified1577swap)
  apply certified_cons (by exact certified1578)
  apply certified_cons (by exact certified1578swap)
  apply certified_cons (by exact certified1579)
  apply certified_cons (by exact certified1579swap)
  apply certified_cons (by exact certified1580)
  apply certified_cons (by exact certified1580swap)
  apply certified_cons (by exact certified1581)
  apply certified_cons (by exact certified1581swap)
  apply certified_cons (by exact certified1582)
  apply certified_cons (by exact certified1582swap)
  apply certified_cons (by exact certified1583)
  apply certified_cons (by exact certified1583swap)
  apply certified_cons (by exact certified1584)
  apply certified_cons (by exact certified1584swap)
  apply certified_cons (by exact certified1585)
  apply certified_cons (by exact certified1585swap)
  apply certified_cons (by exact certified1586)
  apply certified_cons (by exact certified1586swap)
  apply certified_cons (by exact certified1587)
  apply certified_cons (by exact certified1587swap)
  apply certified_cons (by exact certified1588)
  apply certified_cons (by exact certified1588swap)
  apply certified_cons (by exact certified1589)
  apply certified_cons (by exact certified1589swap)
  apply certified_cons (by exact certified1590)
  apply certified_cons (by exact certified1590swap)
  apply certified_cons (by exact certified1591)
  apply certified_cons (by exact certified1591swap)
  apply certified_cons (by exact certified1592)
  apply certified_cons (by exact certified1592swap)
  apply certified_cons (by exact certified1593)
  apply certified_cons (by exact certified1593swap)
  apply certified_cons (by exact certified1594)
  apply certified_cons (by exact certified1594swap)
  apply certified_cons (by exact certified1595)
  apply certified_cons (by exact certified1595swap)
  apply certified_cons (by exact certified1596)
  apply certified_cons (by exact certified1596swap)
  apply certified_cons (by exact certified1597)
  apply certified_cons (by exact certified1597swap)
  apply certified_cons (by exact certified1598)
  apply certified_cons (by exact certified1598swap)
  apply certified_cons (by exact certified1599)
  apply certified_cons (by exact certified1599swap)
  simp
#print axioms certified_keys031
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
