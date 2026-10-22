/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1650
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1651
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1652
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1653
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1654
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1655
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1656
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1657
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1658
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1659
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1660
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1661
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1662
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1663
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1664
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1665
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1666
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1667
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1668
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1669
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1670
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1671
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1672
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1673
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1674
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1675
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1676
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1677
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1678
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1679
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1680
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1681
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1682
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1683
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1684
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1685
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1686
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1687
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1688
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1689
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1690
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1691
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1692
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1693
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1694
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1695
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1696
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1697
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1698
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1699
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys033 : ∀ k ∈ keys033, Certified k := by
  apply certified_cons (by exact certified1650)
  apply certified_cons (by exact certified1650swap)
  apply certified_cons (by exact certified1651)
  apply certified_cons (by exact certified1651swap)
  apply certified_cons (by exact certified1652)
  apply certified_cons (by exact certified1652swap)
  apply certified_cons (by exact certified1653)
  apply certified_cons (by exact certified1653swap)
  apply certified_cons (by exact certified1654)
  apply certified_cons (by exact certified1654swap)
  apply certified_cons (by exact certified1655)
  apply certified_cons (by exact certified1655swap)
  apply certified_cons (by exact certified1656)
  apply certified_cons (by exact certified1656swap)
  apply certified_cons (by exact certified1657)
  apply certified_cons (by exact certified1657swap)
  apply certified_cons (by exact certified1658)
  apply certified_cons (by exact certified1658swap)
  apply certified_cons (by exact certified1659)
  apply certified_cons (by exact certified1659swap)
  apply certified_cons (by exact certified1660)
  apply certified_cons (by exact certified1660swap)
  apply certified_cons (by exact certified1661)
  apply certified_cons (by exact certified1661swap)
  apply certified_cons (by exact certified1662)
  apply certified_cons (by exact certified1662swap)
  apply certified_cons (by exact certified1663)
  apply certified_cons (by exact certified1663swap)
  apply certified_cons (by exact certified1664)
  apply certified_cons (by exact certified1664swap)
  apply certified_cons (by exact certified1665)
  apply certified_cons (by exact certified1665swap)
  apply certified_cons (by exact certified1666)
  apply certified_cons (by exact certified1666swap)
  apply certified_cons (by exact certified1667)
  apply certified_cons (by exact certified1667swap)
  apply certified_cons (by exact certified1668)
  apply certified_cons (by exact certified1668swap)
  apply certified_cons (by exact certified1669)
  apply certified_cons (by exact certified1669swap)
  apply certified_cons (by exact certified1670)
  apply certified_cons (by exact certified1670swap)
  apply certified_cons (by exact certified1671)
  apply certified_cons (by exact certified1671swap)
  apply certified_cons (by exact certified1672)
  apply certified_cons (by exact certified1672swap)
  apply certified_cons (by exact certified1673)
  apply certified_cons (by exact certified1673swap)
  apply certified_cons (by exact certified1674)
  apply certified_cons (by exact certified1674swap)
  apply certified_cons (by exact certified1675)
  apply certified_cons (by exact certified1675swap)
  apply certified_cons (by exact certified1676)
  apply certified_cons (by exact certified1676swap)
  apply certified_cons (by exact certified1677)
  apply certified_cons (by exact certified1677swap)
  apply certified_cons (by exact certified1678)
  apply certified_cons (by exact certified1678swap)
  apply certified_cons (by exact certified1679)
  apply certified_cons (by exact certified1679swap)
  apply certified_cons (by exact certified1680)
  apply certified_cons (by exact certified1680swap)
  apply certified_cons (by exact certified1681)
  apply certified_cons (by exact certified1681swap)
  apply certified_cons (by exact certified1682)
  apply certified_cons (by exact certified1682swap)
  apply certified_cons (by exact certified1683)
  apply certified_cons (by exact certified1683swap)
  apply certified_cons (by exact certified1684)
  apply certified_cons (by exact certified1684swap)
  apply certified_cons (by exact certified1685)
  apply certified_cons (by exact certified1685swap)
  apply certified_cons (by exact certified1686)
  apply certified_cons (by exact certified1686swap)
  apply certified_cons (by exact certified1687)
  apply certified_cons (by exact certified1687swap)
  apply certified_cons (by exact certified1688)
  apply certified_cons (by exact certified1688swap)
  apply certified_cons (by exact certified1689)
  apply certified_cons (by exact certified1689swap)
  apply certified_cons (by exact certified1690)
  apply certified_cons (by exact certified1690swap)
  apply certified_cons (by exact certified1691)
  apply certified_cons (by exact certified1691swap)
  apply certified_cons (by exact certified1692)
  apply certified_cons (by exact certified1692swap)
  apply certified_cons (by exact certified1693)
  apply certified_cons (by exact certified1693swap)
  apply certified_cons (by exact certified1694)
  apply certified_cons (by exact certified1694swap)
  apply certified_cons (by exact certified1695)
  apply certified_cons (by exact certified1695swap)
  apply certified_cons (by exact certified1696)
  apply certified_cons (by exact certified1696swap)
  apply certified_cons (by exact certified1697)
  apply certified_cons (by exact certified1697swap)
  apply certified_cons (by exact certified1698)
  apply certified_cons (by exact certified1698swap)
  apply certified_cons (by exact certified1699)
  apply certified_cons (by exact certified1699swap)
  simp
#print axioms certified_keys033
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
