/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1650
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1651
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1652
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1653
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1654
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1655
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1656
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1657
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1658
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1659
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1660
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1661
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1662
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1663
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1664
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1665
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1666
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1667
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1668
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1669
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1670
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1671
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1672
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1673
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1674
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1675
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1676
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1677
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1678
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1679
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1680
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1681
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1682
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1683
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1684
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1685
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1686
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1687
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1688
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1689
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1690
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1691
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1692
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1693
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1694
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1695
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1696
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1697
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1698
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1699
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys33 : ∀ k ∈ keys33, Certified k := by
  apply certified_cons (by exact certified1650)
  apply certified_cons (by exact certified1650swap)
  apply certified_cons (by exact certified1651)
  apply certified_cons (by exact certified1652)
  apply certified_cons (by exact certified1652swap)
  apply certified_cons (by exact certified1653)
  apply certified_cons (by exact certified1654)
  apply certified_cons (by exact certified1654swap)
  apply certified_cons (by exact certified1655)
  apply certified_cons (by exact certified1656)
  apply certified_cons (by exact certified1656swap)
  apply certified_cons (by exact certified1657)
  apply certified_cons (by exact certified1658)
  apply certified_cons (by exact certified1658swap)
  apply certified_cons (by exact certified1659)
  apply certified_cons (by exact certified1660)
  apply certified_cons (by exact certified1660swap)
  apply certified_cons (by exact certified1661)
  apply certified_cons (by exact certified1662)
  apply certified_cons (by exact certified1662swap)
  apply certified_cons (by exact certified1663)
  apply certified_cons (by exact certified1664)
  apply certified_cons (by exact certified1664swap)
  apply certified_cons (by exact certified1665)
  apply certified_cons (by exact certified1666)
  apply certified_cons (by exact certified1666swap)
  apply certified_cons (by exact certified1667)
  apply certified_cons (by exact certified1668)
  apply certified_cons (by exact certified1668swap)
  apply certified_cons (by exact certified1669)
  apply certified_cons (by exact certified1670)
  apply certified_cons (by exact certified1670swap)
  apply certified_cons (by exact certified1671)
  apply certified_cons (by exact certified1672)
  apply certified_cons (by exact certified1672swap)
  apply certified_cons (by exact certified1673)
  apply certified_cons (by exact certified1674)
  apply certified_cons (by exact certified1674swap)
  apply certified_cons (by exact certified1675)
  apply certified_cons (by exact certified1676)
  apply certified_cons (by exact certified1676swap)
  apply certified_cons (by exact certified1677)
  apply certified_cons (by exact certified1678)
  apply certified_cons (by exact certified1678swap)
  apply certified_cons (by exact certified1679)
  apply certified_cons (by exact certified1680)
  apply certified_cons (by exact certified1680swap)
  apply certified_cons (by exact certified1681)
  apply certified_cons (by exact certified1682)
  apply certified_cons (by exact certified1682swap)
  apply certified_cons (by exact certified1683)
  apply certified_cons (by exact certified1684)
  apply certified_cons (by exact certified1684swap)
  apply certified_cons (by exact certified1685)
  apply certified_cons (by exact certified1686)
  apply certified_cons (by exact certified1686swap)
  apply certified_cons (by exact certified1687)
  apply certified_cons (by exact certified1688)
  apply certified_cons (by exact certified1688swap)
  apply certified_cons (by exact certified1689)
  apply certified_cons (by exact certified1690)
  apply certified_cons (by exact certified1690swap)
  apply certified_cons (by exact certified1691)
  apply certified_cons (by exact certified1692)
  apply certified_cons (by exact certified1692swap)
  apply certified_cons (by exact certified1693)
  apply certified_cons (by exact certified1694)
  apply certified_cons (by exact certified1694swap)
  apply certified_cons (by exact certified1695)
  apply certified_cons (by exact certified1696)
  apply certified_cons (by exact certified1696swap)
  apply certified_cons (by exact certified1697)
  apply certified_cons (by exact certified1698)
  apply certified_cons (by exact certified1698swap)
  apply certified_cons (by exact certified1699)
  simp
#print axioms certified_keys33
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
