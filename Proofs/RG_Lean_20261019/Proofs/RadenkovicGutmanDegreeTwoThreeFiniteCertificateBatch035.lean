/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1750
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1751
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1752
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1753
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1754
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1755
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1756
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1757
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1758
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1759
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1760
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1761
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1762
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1763
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1764
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1765
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1766
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1767
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1768
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1769
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1770
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1771
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1772
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1773
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1774
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1775
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1776
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1777
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1778
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1779
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1780
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1781
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1782
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1783
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1784
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1785
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1786
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1787
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1788
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1789
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1790
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1791
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1792
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1793
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1794
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1795
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1796
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1797
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1798
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1799
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys035 : ∀ k ∈ keys035, Certified k := by
  apply certified_cons (by exact certified1750)
  apply certified_cons (by exact certified1750swap)
  apply certified_cons (by exact certified1751)
  apply certified_cons (by exact certified1751swap)
  apply certified_cons (by exact certified1752)
  apply certified_cons (by exact certified1752swap)
  apply certified_cons (by exact certified1753)
  apply certified_cons (by exact certified1753swap)
  apply certified_cons (by exact certified1754)
  apply certified_cons (by exact certified1754swap)
  apply certified_cons (by exact certified1755)
  apply certified_cons (by exact certified1755swap)
  apply certified_cons (by exact certified1756)
  apply certified_cons (by exact certified1756swap)
  apply certified_cons (by exact certified1757)
  apply certified_cons (by exact certified1757swap)
  apply certified_cons (by exact certified1758)
  apply certified_cons (by exact certified1758swap)
  apply certified_cons (by exact certified1759)
  apply certified_cons (by exact certified1759swap)
  apply certified_cons (by exact certified1760)
  apply certified_cons (by exact certified1760swap)
  apply certified_cons (by exact certified1761)
  apply certified_cons (by exact certified1761swap)
  apply certified_cons (by exact certified1762)
  apply certified_cons (by exact certified1762swap)
  apply certified_cons (by exact certified1763)
  apply certified_cons (by exact certified1763swap)
  apply certified_cons (by exact certified1764)
  apply certified_cons (by exact certified1764swap)
  apply certified_cons (by exact certified1765)
  apply certified_cons (by exact certified1765swap)
  apply certified_cons (by exact certified1766)
  apply certified_cons (by exact certified1766swap)
  apply certified_cons (by exact certified1767)
  apply certified_cons (by exact certified1767swap)
  apply certified_cons (by exact certified1768)
  apply certified_cons (by exact certified1768swap)
  apply certified_cons (by exact certified1769)
  apply certified_cons (by exact certified1769swap)
  apply certified_cons (by exact certified1770)
  apply certified_cons (by exact certified1770swap)
  apply certified_cons (by exact certified1771)
  apply certified_cons (by exact certified1771swap)
  apply certified_cons (by exact certified1772)
  apply certified_cons (by exact certified1772swap)
  apply certified_cons (by exact certified1773)
  apply certified_cons (by exact certified1773swap)
  apply certified_cons (by exact certified1774)
  apply certified_cons (by exact certified1774swap)
  apply certified_cons (by exact certified1775)
  apply certified_cons (by exact certified1775swap)
  apply certified_cons (by exact certified1776)
  apply certified_cons (by exact certified1776swap)
  apply certified_cons (by exact certified1777)
  apply certified_cons (by exact certified1777swap)
  apply certified_cons (by exact certified1778)
  apply certified_cons (by exact certified1778swap)
  apply certified_cons (by exact certified1779)
  apply certified_cons (by exact certified1779swap)
  apply certified_cons (by exact certified1780)
  apply certified_cons (by exact certified1780swap)
  apply certified_cons (by exact certified1781)
  apply certified_cons (by exact certified1781swap)
  apply certified_cons (by exact certified1782)
  apply certified_cons (by exact certified1782swap)
  apply certified_cons (by exact certified1783)
  apply certified_cons (by exact certified1783swap)
  apply certified_cons (by exact certified1784)
  apply certified_cons (by exact certified1784swap)
  apply certified_cons (by exact certified1785)
  apply certified_cons (by exact certified1785swap)
  apply certified_cons (by exact certified1786)
  apply certified_cons (by exact certified1786swap)
  apply certified_cons (by exact certified1787)
  apply certified_cons (by exact certified1787swap)
  apply certified_cons (by exact certified1788)
  apply certified_cons (by exact certified1788swap)
  apply certified_cons (by exact certified1789)
  apply certified_cons (by exact certified1789swap)
  apply certified_cons (by exact certified1790)
  apply certified_cons (by exact certified1790swap)
  apply certified_cons (by exact certified1791)
  apply certified_cons (by exact certified1791swap)
  apply certified_cons (by exact certified1792)
  apply certified_cons (by exact certified1792swap)
  apply certified_cons (by exact certified1793)
  apply certified_cons (by exact certified1793swap)
  apply certified_cons (by exact certified1794)
  apply certified_cons (by exact certified1794swap)
  apply certified_cons (by exact certified1795)
  apply certified_cons (by exact certified1795swap)
  apply certified_cons (by exact certified1796)
  apply certified_cons (by exact certified1796swap)
  apply certified_cons (by exact certified1797)
  apply certified_cons (by exact certified1797swap)
  apply certified_cons (by exact certified1798)
  apply certified_cons (by exact certified1798swap)
  apply certified_cons (by exact certified1799)
  apply certified_cons (by exact certified1799swap)
  simp
#print axioms certified_keys035
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
