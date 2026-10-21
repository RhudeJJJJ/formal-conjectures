/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1800
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1801
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1802
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1803
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1804
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1805
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1806
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1807
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1808
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1809
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1810
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1811
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1812
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1813
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1814
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1815
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1816
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1817
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1818
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1819
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1820
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1821
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1822
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1823
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1824
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1825
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1826
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1827
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1828
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1829
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1830
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1831
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1832
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1833
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1834
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1835
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1836
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1837
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1838
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1839
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1840
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1841
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1842
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1843
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1844
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1845
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1846
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1847
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1848
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1849
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys36 : ∀ k ∈ keys36, Certified k := by
  apply certified_cons (by exact certified1800)
  apply certified_cons (by exact certified1801)
  apply certified_cons (by exact certified1802)
  apply certified_cons (by exact certified1803)
  apply certified_cons (by exact certified1804)
  apply certified_cons (by exact certified1805)
  apply certified_cons (by exact certified1806)
  apply certified_cons (by exact certified1807)
  apply certified_cons (by exact certified1808)
  apply certified_cons (by exact certified1809)
  apply certified_cons (by exact certified1810)
  apply certified_cons (by exact certified1811)
  apply certified_cons (by exact certified1812)
  apply certified_cons (by exact certified1813)
  apply certified_cons (by exact certified1814)
  apply certified_cons (by exact certified1815)
  apply certified_cons (by exact certified1816)
  apply certified_cons (by exact certified1817)
  apply certified_cons (by exact certified1818)
  apply certified_cons (by exact certified1819)
  apply certified_cons (by exact certified1820)
  apply certified_cons (by exact certified1821)
  apply certified_cons (by exact certified1822)
  apply certified_cons (by exact certified1823)
  apply certified_cons (by exact certified1824)
  apply certified_cons (by exact certified1825)
  apply certified_cons (by exact certified1826)
  apply certified_cons (by exact certified1827)
  apply certified_cons (by exact certified1828)
  apply certified_cons (by exact certified1829)
  apply certified_cons (by exact certified1830)
  apply certified_cons (by exact certified1831)
  apply certified_cons (by exact certified1832)
  apply certified_cons (by exact certified1833)
  apply certified_cons (by exact certified1834)
  apply certified_cons (by exact certified1835)
  apply certified_cons (by exact certified1836)
  apply certified_cons (by exact certified1837)
  apply certified_cons (by exact certified1838)
  apply certified_cons (by exact certified1839)
  apply certified_cons (by exact certified1840)
  apply certified_cons (by exact certified1841)
  apply certified_cons (by exact certified1842)
  apply certified_cons (by exact certified1843)
  apply certified_cons (by exact certified1844)
  apply certified_cons (by exact certified1845)
  apply certified_cons (by exact certified1846)
  apply certified_cons (by exact certified1847)
  apply certified_cons (by exact certified1848)
  apply certified_cons (by exact certified1849)
  simp
#print axioms certified_keys36
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
