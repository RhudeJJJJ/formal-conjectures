/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1850
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1851
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1852
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1853
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1854
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1855
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1856
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1857
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1858
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1859
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1860
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1861
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1862
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1863
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1864
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1865
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1866
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1867
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1868
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1869
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1870
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1871
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1872
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1873
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1874
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1875
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1876
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1877
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1878
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1879
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1880
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1881
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1882
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1883
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1884
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1885
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1886
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1887
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1888
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1889
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1890
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1891
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1892
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1893
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1894
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1895
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1896
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1897
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1898
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1899
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys037 : ∀ k ∈ keys037, Certified k := by
  apply certified_cons (by exact certified1850)
  apply certified_cons (by exact certified1850swap)
  apply certified_cons (by exact certified1851)
  apply certified_cons (by exact certified1851swap)
  apply certified_cons (by exact certified1852)
  apply certified_cons (by exact certified1852swap)
  apply certified_cons (by exact certified1853)
  apply certified_cons (by exact certified1853swap)
  apply certified_cons (by exact certified1854)
  apply certified_cons (by exact certified1854swap)
  apply certified_cons (by exact certified1855)
  apply certified_cons (by exact certified1855swap)
  apply certified_cons (by exact certified1856)
  apply certified_cons (by exact certified1856swap)
  apply certified_cons (by exact certified1857)
  apply certified_cons (by exact certified1857swap)
  apply certified_cons (by exact certified1858)
  apply certified_cons (by exact certified1858swap)
  apply certified_cons (by exact certified1859)
  apply certified_cons (by exact certified1859swap)
  apply certified_cons (by exact certified1860)
  apply certified_cons (by exact certified1860swap)
  apply certified_cons (by exact certified1861)
  apply certified_cons (by exact certified1861swap)
  apply certified_cons (by exact certified1862)
  apply certified_cons (by exact certified1862swap)
  apply certified_cons (by exact certified1863)
  apply certified_cons (by exact certified1863swap)
  apply certified_cons (by exact certified1864)
  apply certified_cons (by exact certified1864swap)
  apply certified_cons (by exact certified1865)
  apply certified_cons (by exact certified1865swap)
  apply certified_cons (by exact certified1866)
  apply certified_cons (by exact certified1866swap)
  apply certified_cons (by exact certified1867)
  apply certified_cons (by exact certified1867swap)
  apply certified_cons (by exact certified1868)
  apply certified_cons (by exact certified1868swap)
  apply certified_cons (by exact certified1869)
  apply certified_cons (by exact certified1869swap)
  apply certified_cons (by exact certified1870)
  apply certified_cons (by exact certified1870swap)
  apply certified_cons (by exact certified1871)
  apply certified_cons (by exact certified1871swap)
  apply certified_cons (by exact certified1872)
  apply certified_cons (by exact certified1872swap)
  apply certified_cons (by exact certified1873)
  apply certified_cons (by exact certified1873swap)
  apply certified_cons (by exact certified1874)
  apply certified_cons (by exact certified1874swap)
  apply certified_cons (by exact certified1875)
  apply certified_cons (by exact certified1875swap)
  apply certified_cons (by exact certified1876)
  apply certified_cons (by exact certified1876swap)
  apply certified_cons (by exact certified1877)
  apply certified_cons (by exact certified1877swap)
  apply certified_cons (by exact certified1878)
  apply certified_cons (by exact certified1878swap)
  apply certified_cons (by exact certified1879)
  apply certified_cons (by exact certified1879swap)
  apply certified_cons (by exact certified1880)
  apply certified_cons (by exact certified1880swap)
  apply certified_cons (by exact certified1881)
  apply certified_cons (by exact certified1881swap)
  apply certified_cons (by exact certified1882)
  apply certified_cons (by exact certified1882swap)
  apply certified_cons (by exact certified1883)
  apply certified_cons (by exact certified1883swap)
  apply certified_cons (by exact certified1884)
  apply certified_cons (by exact certified1884swap)
  apply certified_cons (by exact certified1885)
  apply certified_cons (by exact certified1885swap)
  apply certified_cons (by exact certified1886)
  apply certified_cons (by exact certified1886swap)
  apply certified_cons (by exact certified1887)
  apply certified_cons (by exact certified1887swap)
  apply certified_cons (by exact certified1888)
  apply certified_cons (by exact certified1888swap)
  apply certified_cons (by exact certified1889)
  apply certified_cons (by exact certified1889swap)
  apply certified_cons (by exact certified1890)
  apply certified_cons (by exact certified1890swap)
  apply certified_cons (by exact certified1891)
  apply certified_cons (by exact certified1891swap)
  apply certified_cons (by exact certified1892)
  apply certified_cons (by exact certified1892swap)
  apply certified_cons (by exact certified1893)
  apply certified_cons (by exact certified1893swap)
  apply certified_cons (by exact certified1894)
  apply certified_cons (by exact certified1894swap)
  apply certified_cons (by exact certified1895)
  apply certified_cons (by exact certified1895swap)
  apply certified_cons (by exact certified1896)
  apply certified_cons (by exact certified1896swap)
  apply certified_cons (by exact certified1897)
  apply certified_cons (by exact certified1897swap)
  apply certified_cons (by exact certified1898)
  apply certified_cons (by exact certified1898swap)
  apply certified_cons (by exact certified1899)
  apply certified_cons (by exact certified1899swap)
  simp
#print axioms certified_keys037
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
