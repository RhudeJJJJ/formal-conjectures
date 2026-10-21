/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1900
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1901
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1902
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1903
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1904
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1905
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1906
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1907
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1908
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1909
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1910
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1911
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1912
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1913
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1914
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1915
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1916
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1917
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1918
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1919
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1920
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1921
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1922
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1923
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1924
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1925
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1926
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1927
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1928
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1929
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1930
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1931
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1932
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1933
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1934
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1935
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1936
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1937
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1938
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1939
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1940
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1941
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1942
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1943
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1944
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1945
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1946
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1947
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1948
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1949
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys38 : ∀ k ∈ keys38, Certified k := by
  apply certified_cons (by exact certified1900)
  apply certified_cons (by exact certified1901)
  apply certified_cons (by exact certified1902)
  apply certified_cons (by exact certified1903)
  apply certified_cons (by exact certified1904)
  apply certified_cons (by exact certified1905)
  apply certified_cons (by exact certified1906)
  apply certified_cons (by exact certified1907)
  apply certified_cons (by exact certified1908)
  apply certified_cons (by exact certified1909)
  apply certified_cons (by exact certified1910)
  apply certified_cons (by exact certified1911)
  apply certified_cons (by exact certified1912)
  apply certified_cons (by exact certified1913)
  apply certified_cons (by exact certified1914)
  apply certified_cons (by exact certified1915)
  apply certified_cons (by exact certified1916)
  apply certified_cons (by exact certified1917)
  apply certified_cons (by exact certified1918)
  apply certified_cons (by exact certified1919)
  apply certified_cons (by exact certified1920)
  apply certified_cons (by exact certified1921)
  apply certified_cons (by exact certified1922)
  apply certified_cons (by exact certified1923)
  apply certified_cons (by exact certified1924)
  apply certified_cons (by exact certified1925)
  apply certified_cons (by exact certified1926)
  apply certified_cons (by exact certified1927)
  apply certified_cons (by exact certified1928)
  apply certified_cons (by exact certified1929)
  apply certified_cons (by exact certified1930)
  apply certified_cons (by exact certified1931)
  apply certified_cons (by exact certified1932)
  apply certified_cons (by exact certified1933)
  apply certified_cons (by exact certified1934)
  apply certified_cons (by exact certified1935)
  apply certified_cons (by exact certified1936)
  apply certified_cons (by exact certified1937)
  apply certified_cons (by exact certified1938)
  apply certified_cons (by exact certified1939)
  apply certified_cons (by exact certified1940)
  apply certified_cons (by exact certified1941)
  apply certified_cons (by exact certified1942)
  apply certified_cons (by exact certified1943)
  apply certified_cons (by exact certified1944)
  apply certified_cons (by exact certified1945)
  apply certified_cons (by exact certified1946)
  apply certified_cons (by exact certified1947)
  apply certified_cons (by exact certified1948)
  apply certified_cons (by exact certified1949)
  simp
#print axioms certified_keys38
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
