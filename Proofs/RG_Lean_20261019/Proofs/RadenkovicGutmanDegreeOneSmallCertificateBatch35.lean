/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1750
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1751
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1752
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1753
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1754
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1755
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1756
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1757
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1758
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1759
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1760
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1761
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1762
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1763
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1764
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1765
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1766
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1767
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1768
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1769
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1770
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1771
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1772
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1773
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1774
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1775
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1776
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1777
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1778
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1779
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1780
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1781
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1782
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1783
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1784
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1785
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1786
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1787
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1788
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1789
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1790
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1791
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1792
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1793
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1794
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1795
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1796
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1797
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1798
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1799
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys35 : ∀ k ∈ keys35, Certified k := by
  apply certified_cons (by exact certified1750)
  apply certified_cons (by exact certified1750swap)
  apply certified_cons (by exact certified1751)
  apply certified_cons (by exact certified1752)
  apply certified_cons (by exact certified1752swap)
  apply certified_cons (by exact certified1753)
  apply certified_cons (by exact certified1754)
  apply certified_cons (by exact certified1754swap)
  apply certified_cons (by exact certified1755)
  apply certified_cons (by exact certified1756)
  apply certified_cons (by exact certified1756swap)
  apply certified_cons (by exact certified1757)
  apply certified_cons (by exact certified1758)
  apply certified_cons (by exact certified1758swap)
  apply certified_cons (by exact certified1759)
  apply certified_cons (by exact certified1760)
  apply certified_cons (by exact certified1760swap)
  apply certified_cons (by exact certified1761)
  apply certified_cons (by exact certified1762)
  apply certified_cons (by exact certified1762swap)
  apply certified_cons (by exact certified1763)
  apply certified_cons (by exact certified1764)
  apply certified_cons (by exact certified1764swap)
  apply certified_cons (by exact certified1765)
  apply certified_cons (by exact certified1766)
  apply certified_cons (by exact certified1766swap)
  apply certified_cons (by exact certified1767)
  apply certified_cons (by exact certified1768)
  apply certified_cons (by exact certified1769)
  apply certified_cons (by exact certified1770)
  apply certified_cons (by exact certified1771)
  apply certified_cons (by exact certified1772)
  apply certified_cons (by exact certified1773)
  apply certified_cons (by exact certified1774)
  apply certified_cons (by exact certified1775)
  apply certified_cons (by exact certified1776)
  apply certified_cons (by exact certified1777)
  apply certified_cons (by exact certified1778)
  apply certified_cons (by exact certified1779)
  apply certified_cons (by exact certified1780)
  apply certified_cons (by exact certified1781)
  apply certified_cons (by exact certified1782)
  apply certified_cons (by exact certified1783)
  apply certified_cons (by exact certified1784)
  apply certified_cons (by exact certified1785)
  apply certified_cons (by exact certified1786)
  apply certified_cons (by exact certified1787)
  apply certified_cons (by exact certified1788)
  apply certified_cons (by exact certified1789)
  apply certified_cons (by exact certified1790)
  apply certified_cons (by exact certified1791)
  apply certified_cons (by exact certified1792)
  apply certified_cons (by exact certified1793)
  apply certified_cons (by exact certified1794)
  apply certified_cons (by exact certified1795)
  apply certified_cons (by exact certified1796)
  apply certified_cons (by exact certified1797)
  apply certified_cons (by exact certified1798)
  apply certified_cons (by exact certified1799)
  simp
#print axioms certified_keys35
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
