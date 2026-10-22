/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1800
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1801
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1802
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1803
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1804
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1805
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1806
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1807
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1808
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1809
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1810
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1811
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1812
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1813
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1814
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1815
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1816
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1817
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1818
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1819
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1820
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1821
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1822
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1823
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1824
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1825
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1826
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1827
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1828
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1829
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1830
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1831
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1832
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1833
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1834
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1835
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1836
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1837
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1838
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1839
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1840
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1841
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1842
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1843
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1844
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1845
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1846
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1847
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1848
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1849
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys036 : ∀ k ∈ keys036, Certified k := by
  apply certified_cons (by exact certified1800)
  apply certified_cons (by exact certified1800swap)
  apply certified_cons (by exact certified1801)
  apply certified_cons (by exact certified1801swap)
  apply certified_cons (by exact certified1802)
  apply certified_cons (by exact certified1802swap)
  apply certified_cons (by exact certified1803)
  apply certified_cons (by exact certified1803swap)
  apply certified_cons (by exact certified1804)
  apply certified_cons (by exact certified1804swap)
  apply certified_cons (by exact certified1805)
  apply certified_cons (by exact certified1805swap)
  apply certified_cons (by exact certified1806)
  apply certified_cons (by exact certified1806swap)
  apply certified_cons (by exact certified1807)
  apply certified_cons (by exact certified1807swap)
  apply certified_cons (by exact certified1808)
  apply certified_cons (by exact certified1808swap)
  apply certified_cons (by exact certified1809)
  apply certified_cons (by exact certified1809swap)
  apply certified_cons (by exact certified1810)
  apply certified_cons (by exact certified1810swap)
  apply certified_cons (by exact certified1811)
  apply certified_cons (by exact certified1811swap)
  apply certified_cons (by exact certified1812)
  apply certified_cons (by exact certified1812swap)
  apply certified_cons (by exact certified1813)
  apply certified_cons (by exact certified1813swap)
  apply certified_cons (by exact certified1814)
  apply certified_cons (by exact certified1814swap)
  apply certified_cons (by exact certified1815)
  apply certified_cons (by exact certified1815swap)
  apply certified_cons (by exact certified1816)
  apply certified_cons (by exact certified1816swap)
  apply certified_cons (by exact certified1817)
  apply certified_cons (by exact certified1817swap)
  apply certified_cons (by exact certified1818)
  apply certified_cons (by exact certified1818swap)
  apply certified_cons (by exact certified1819)
  apply certified_cons (by exact certified1819swap)
  apply certified_cons (by exact certified1820)
  apply certified_cons (by exact certified1820swap)
  apply certified_cons (by exact certified1821)
  apply certified_cons (by exact certified1821swap)
  apply certified_cons (by exact certified1822)
  apply certified_cons (by exact certified1822swap)
  apply certified_cons (by exact certified1823)
  apply certified_cons (by exact certified1823swap)
  apply certified_cons (by exact certified1824)
  apply certified_cons (by exact certified1824swap)
  apply certified_cons (by exact certified1825)
  apply certified_cons (by exact certified1825swap)
  apply certified_cons (by exact certified1826)
  apply certified_cons (by exact certified1826swap)
  apply certified_cons (by exact certified1827)
  apply certified_cons (by exact certified1827swap)
  apply certified_cons (by exact certified1828)
  apply certified_cons (by exact certified1828swap)
  apply certified_cons (by exact certified1829)
  apply certified_cons (by exact certified1829swap)
  apply certified_cons (by exact certified1830)
  apply certified_cons (by exact certified1830swap)
  apply certified_cons (by exact certified1831)
  apply certified_cons (by exact certified1831swap)
  apply certified_cons (by exact certified1832)
  apply certified_cons (by exact certified1832swap)
  apply certified_cons (by exact certified1833)
  apply certified_cons (by exact certified1833swap)
  apply certified_cons (by exact certified1834)
  apply certified_cons (by exact certified1834swap)
  apply certified_cons (by exact certified1835)
  apply certified_cons (by exact certified1835swap)
  apply certified_cons (by exact certified1836)
  apply certified_cons (by exact certified1836swap)
  apply certified_cons (by exact certified1837)
  apply certified_cons (by exact certified1837swap)
  apply certified_cons (by exact certified1838)
  apply certified_cons (by exact certified1838swap)
  apply certified_cons (by exact certified1839)
  apply certified_cons (by exact certified1839swap)
  apply certified_cons (by exact certified1840)
  apply certified_cons (by exact certified1840swap)
  apply certified_cons (by exact certified1841)
  apply certified_cons (by exact certified1841swap)
  apply certified_cons (by exact certified1842)
  apply certified_cons (by exact certified1842swap)
  apply certified_cons (by exact certified1843)
  apply certified_cons (by exact certified1843swap)
  apply certified_cons (by exact certified1844)
  apply certified_cons (by exact certified1844swap)
  apply certified_cons (by exact certified1845)
  apply certified_cons (by exact certified1845swap)
  apply certified_cons (by exact certified1846)
  apply certified_cons (by exact certified1846swap)
  apply certified_cons (by exact certified1847)
  apply certified_cons (by exact certified1847swap)
  apply certified_cons (by exact certified1848)
  apply certified_cons (by exact certified1848swap)
  apply certified_cons (by exact certified1849)
  apply certified_cons (by exact certified1849swap)
  simp
#print axioms certified_keys036
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
