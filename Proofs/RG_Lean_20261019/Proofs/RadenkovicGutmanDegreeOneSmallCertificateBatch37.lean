/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1850
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1851
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1852
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1853
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1854
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1855
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1856
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1857
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1858
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1859
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1860
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1861
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1862
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1863
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1864
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1865
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1866
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1867
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1868
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1869
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1870
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1871
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1872
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1873
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1874
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1875
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1876
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1877
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1878
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1879
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1880
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1881
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1882
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1883
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1884
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1885
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1886
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1887
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1888
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1889
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1890
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1891
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1892
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1893
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1894
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1895
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1896
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1897
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1898
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1899
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys37 : ∀ k ∈ keys37, Certified k := by
  apply certified_cons (by exact certified1850)
  apply certified_cons (by exact certified1851)
  apply certified_cons (by exact certified1852)
  apply certified_cons (by exact certified1853)
  apply certified_cons (by exact certified1854)
  apply certified_cons (by exact certified1855)
  apply certified_cons (by exact certified1856)
  apply certified_cons (by exact certified1857)
  apply certified_cons (by exact certified1858)
  apply certified_cons (by exact certified1859)
  apply certified_cons (by exact certified1860)
  apply certified_cons (by exact certified1861)
  apply certified_cons (by exact certified1862)
  apply certified_cons (by exact certified1863)
  apply certified_cons (by exact certified1864)
  apply certified_cons (by exact certified1865)
  apply certified_cons (by exact certified1866)
  apply certified_cons (by exact certified1867)
  apply certified_cons (by exact certified1868)
  apply certified_cons (by exact certified1869)
  apply certified_cons (by exact certified1870)
  apply certified_cons (by exact certified1871)
  apply certified_cons (by exact certified1872)
  apply certified_cons (by exact certified1873)
  apply certified_cons (by exact certified1874)
  apply certified_cons (by exact certified1875)
  apply certified_cons (by exact certified1876)
  apply certified_cons (by exact certified1877)
  apply certified_cons (by exact certified1878)
  apply certified_cons (by exact certified1879)
  apply certified_cons (by exact certified1880)
  apply certified_cons (by exact certified1881)
  apply certified_cons (by exact certified1882)
  apply certified_cons (by exact certified1883)
  apply certified_cons (by exact certified1884)
  apply certified_cons (by exact certified1885)
  apply certified_cons (by exact certified1886)
  apply certified_cons (by exact certified1887)
  apply certified_cons (by exact certified1888)
  apply certified_cons (by exact certified1889)
  apply certified_cons (by exact certified1890)
  apply certified_cons (by exact certified1891)
  apply certified_cons (by exact certified1892)
  apply certified_cons (by exact certified1893)
  apply certified_cons (by exact certified1894)
  apply certified_cons (by exact certified1895)
  apply certified_cons (by exact certified1896)
  apply certified_cons (by exact certified1897)
  apply certified_cons (by exact certified1898)
  apply certified_cons (by exact certified1899)
  simp
#print axioms certified_keys37
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
