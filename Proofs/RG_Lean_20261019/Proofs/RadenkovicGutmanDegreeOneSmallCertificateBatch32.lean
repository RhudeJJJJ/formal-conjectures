/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1600
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1601
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1602
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1603
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1604
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1605
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1606
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1607
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1608
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1609
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1610
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1611
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1612
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1613
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1614
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1615
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1616
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1617
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1618
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1619
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1620
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1621
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1622
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1623
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1624
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1625
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1626
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1627
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1628
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1629
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1630
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1631
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1632
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1633
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1634
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1635
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1636
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1637
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1638
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1639
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1640
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1641
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1642
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1643
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1644
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1645
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1646
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1647
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1648
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1649
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys32 : ∀ k ∈ keys32, Certified k := by
  apply certified_cons (by exact certified1600)
  apply certified_cons (by exact certified1600swap)
  apply certified_cons (by exact certified1601)
  apply certified_cons (by exact certified1602)
  apply certified_cons (by exact certified1602swap)
  apply certified_cons (by exact certified1603)
  apply certified_cons (by exact certified1604)
  apply certified_cons (by exact certified1604swap)
  apply certified_cons (by exact certified1605)
  apply certified_cons (by exact certified1606)
  apply certified_cons (by exact certified1606swap)
  apply certified_cons (by exact certified1607)
  apply certified_cons (by exact certified1608)
  apply certified_cons (by exact certified1608swap)
  apply certified_cons (by exact certified1609)
  apply certified_cons (by exact certified1610)
  apply certified_cons (by exact certified1610swap)
  apply certified_cons (by exact certified1611)
  apply certified_cons (by exact certified1612)
  apply certified_cons (by exact certified1612swap)
  apply certified_cons (by exact certified1613)
  apply certified_cons (by exact certified1614)
  apply certified_cons (by exact certified1614swap)
  apply certified_cons (by exact certified1615)
  apply certified_cons (by exact certified1616)
  apply certified_cons (by exact certified1616swap)
  apply certified_cons (by exact certified1617)
  apply certified_cons (by exact certified1618)
  apply certified_cons (by exact certified1618swap)
  apply certified_cons (by exact certified1619)
  apply certified_cons (by exact certified1620)
  apply certified_cons (by exact certified1620swap)
  apply certified_cons (by exact certified1621)
  apply certified_cons (by exact certified1622)
  apply certified_cons (by exact certified1622swap)
  apply certified_cons (by exact certified1623)
  apply certified_cons (by exact certified1624)
  apply certified_cons (by exact certified1624swap)
  apply certified_cons (by exact certified1625)
  apply certified_cons (by exact certified1626)
  apply certified_cons (by exact certified1626swap)
  apply certified_cons (by exact certified1627)
  apply certified_cons (by exact certified1628)
  apply certified_cons (by exact certified1628swap)
  apply certified_cons (by exact certified1629)
  apply certified_cons (by exact certified1630)
  apply certified_cons (by exact certified1630swap)
  apply certified_cons (by exact certified1631)
  apply certified_cons (by exact certified1632)
  apply certified_cons (by exact certified1632swap)
  apply certified_cons (by exact certified1633)
  apply certified_cons (by exact certified1634)
  apply certified_cons (by exact certified1634swap)
  apply certified_cons (by exact certified1635)
  apply certified_cons (by exact certified1636)
  apply certified_cons (by exact certified1636swap)
  apply certified_cons (by exact certified1637)
  apply certified_cons (by exact certified1638)
  apply certified_cons (by exact certified1638swap)
  apply certified_cons (by exact certified1639)
  apply certified_cons (by exact certified1640)
  apply certified_cons (by exact certified1640swap)
  apply certified_cons (by exact certified1641)
  apply certified_cons (by exact certified1642)
  apply certified_cons (by exact certified1642swap)
  apply certified_cons (by exact certified1643)
  apply certified_cons (by exact certified1644)
  apply certified_cons (by exact certified1644swap)
  apply certified_cons (by exact certified1645)
  apply certified_cons (by exact certified1646)
  apply certified_cons (by exact certified1646swap)
  apply certified_cons (by exact certified1647)
  apply certified_cons (by exact certified1648)
  apply certified_cons (by exact certified1648swap)
  apply certified_cons (by exact certified1649)
  simp
#print axioms certified_keys32
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
