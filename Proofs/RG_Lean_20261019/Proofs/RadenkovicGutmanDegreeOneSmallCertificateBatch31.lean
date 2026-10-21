/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1550
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1551
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1552
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1553
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1554
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1555
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1556
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1557
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1558
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1559
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1560
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1561
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1562
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1563
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1564
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1565
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1566
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1567
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1568
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1569
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1570
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1571
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1572
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1573
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1574
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1575
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1576
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1577
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1578
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1579
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1580
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1581
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1582
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1583
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1584
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1585
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1586
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1587
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1588
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1589
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1590
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1591
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1592
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1593
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1594
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1595
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1596
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1597
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1598
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1599
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys31 : ∀ k ∈ keys31, Certified k := by
  apply certified_cons (by exact certified1550)
  apply certified_cons (by exact certified1550swap)
  apply certified_cons (by exact certified1551)
  apply certified_cons (by exact certified1552)
  apply certified_cons (by exact certified1552swap)
  apply certified_cons (by exact certified1553)
  apply certified_cons (by exact certified1554)
  apply certified_cons (by exact certified1554swap)
  apply certified_cons (by exact certified1555)
  apply certified_cons (by exact certified1556)
  apply certified_cons (by exact certified1556swap)
  apply certified_cons (by exact certified1557)
  apply certified_cons (by exact certified1558)
  apply certified_cons (by exact certified1558swap)
  apply certified_cons (by exact certified1559)
  apply certified_cons (by exact certified1560)
  apply certified_cons (by exact certified1560swap)
  apply certified_cons (by exact certified1561)
  apply certified_cons (by exact certified1562)
  apply certified_cons (by exact certified1562swap)
  apply certified_cons (by exact certified1563)
  apply certified_cons (by exact certified1564)
  apply certified_cons (by exact certified1564swap)
  apply certified_cons (by exact certified1565)
  apply certified_cons (by exact certified1566)
  apply certified_cons (by exact certified1566swap)
  apply certified_cons (by exact certified1567)
  apply certified_cons (by exact certified1568)
  apply certified_cons (by exact certified1568swap)
  apply certified_cons (by exact certified1569)
  apply certified_cons (by exact certified1570)
  apply certified_cons (by exact certified1570swap)
  apply certified_cons (by exact certified1571)
  apply certified_cons (by exact certified1572)
  apply certified_cons (by exact certified1572swap)
  apply certified_cons (by exact certified1573)
  apply certified_cons (by exact certified1574)
  apply certified_cons (by exact certified1574swap)
  apply certified_cons (by exact certified1575)
  apply certified_cons (by exact certified1576)
  apply certified_cons (by exact certified1576swap)
  apply certified_cons (by exact certified1577)
  apply certified_cons (by exact certified1578)
  apply certified_cons (by exact certified1578swap)
  apply certified_cons (by exact certified1579)
  apply certified_cons (by exact certified1580)
  apply certified_cons (by exact certified1580swap)
  apply certified_cons (by exact certified1581)
  apply certified_cons (by exact certified1582)
  apply certified_cons (by exact certified1582swap)
  apply certified_cons (by exact certified1583)
  apply certified_cons (by exact certified1584)
  apply certified_cons (by exact certified1584swap)
  apply certified_cons (by exact certified1585)
  apply certified_cons (by exact certified1586)
  apply certified_cons (by exact certified1586swap)
  apply certified_cons (by exact certified1587)
  apply certified_cons (by exact certified1588)
  apply certified_cons (by exact certified1588swap)
  apply certified_cons (by exact certified1589)
  apply certified_cons (by exact certified1590)
  apply certified_cons (by exact certified1590swap)
  apply certified_cons (by exact certified1591)
  apply certified_cons (by exact certified1592)
  apply certified_cons (by exact certified1592swap)
  apply certified_cons (by exact certified1593)
  apply certified_cons (by exact certified1594)
  apply certified_cons (by exact certified1594swap)
  apply certified_cons (by exact certified1595)
  apply certified_cons (by exact certified1596)
  apply certified_cons (by exact certified1596swap)
  apply certified_cons (by exact certified1597)
  apply certified_cons (by exact certified1598)
  apply certified_cons (by exact certified1598swap)
  apply certified_cons (by exact certified1599)
  simp
#print axioms certified_keys31
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
