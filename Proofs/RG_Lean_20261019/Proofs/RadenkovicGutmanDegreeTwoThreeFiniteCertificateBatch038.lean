/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1900
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1901
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1902
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1903
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1904
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1905
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1906
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1907
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1908
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1909
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1910
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1911
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1912
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1913
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1914
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1915
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1916
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1917
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1918
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1919
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1920
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1921
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1922
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1923
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1924
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1925
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1926
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1927
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1928
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1929
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1930
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1931
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1932
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1933
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1934
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1935
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1936
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1937
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1938
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1939
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1940
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1941
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1942
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1943
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1944
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1945
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1946
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1947
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1948
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1949
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys038 : ∀ k ∈ keys038, Certified k := by
  apply certified_cons (by exact certified1900)
  apply certified_cons (by exact certified1900swap)
  apply certified_cons (by exact certified1901)
  apply certified_cons (by exact certified1901swap)
  apply certified_cons (by exact certified1902)
  apply certified_cons (by exact certified1902swap)
  apply certified_cons (by exact certified1903)
  apply certified_cons (by exact certified1903swap)
  apply certified_cons (by exact certified1904)
  apply certified_cons (by exact certified1904swap)
  apply certified_cons (by exact certified1905)
  apply certified_cons (by exact certified1905swap)
  apply certified_cons (by exact certified1906)
  apply certified_cons (by exact certified1906swap)
  apply certified_cons (by exact certified1907)
  apply certified_cons (by exact certified1907swap)
  apply certified_cons (by exact certified1908)
  apply certified_cons (by exact certified1908swap)
  apply certified_cons (by exact certified1909)
  apply certified_cons (by exact certified1909swap)
  apply certified_cons (by exact certified1910)
  apply certified_cons (by exact certified1910swap)
  apply certified_cons (by exact certified1911)
  apply certified_cons (by exact certified1911swap)
  apply certified_cons (by exact certified1912)
  apply certified_cons (by exact certified1912swap)
  apply certified_cons (by exact certified1913)
  apply certified_cons (by exact certified1913swap)
  apply certified_cons (by exact certified1914)
  apply certified_cons (by exact certified1914swap)
  apply certified_cons (by exact certified1915)
  apply certified_cons (by exact certified1915swap)
  apply certified_cons (by exact certified1916)
  apply certified_cons (by exact certified1916swap)
  apply certified_cons (by exact certified1917)
  apply certified_cons (by exact certified1917swap)
  apply certified_cons (by exact certified1918)
  apply certified_cons (by exact certified1918swap)
  apply certified_cons (by exact certified1919)
  apply certified_cons (by exact certified1919swap)
  apply certified_cons (by exact certified1920)
  apply certified_cons (by exact certified1920swap)
  apply certified_cons (by exact certified1921)
  apply certified_cons (by exact certified1921swap)
  apply certified_cons (by exact certified1922)
  apply certified_cons (by exact certified1922swap)
  apply certified_cons (by exact certified1923)
  apply certified_cons (by exact certified1923swap)
  apply certified_cons (by exact certified1924)
  apply certified_cons (by exact certified1924swap)
  apply certified_cons (by exact certified1925)
  apply certified_cons (by exact certified1925swap)
  apply certified_cons (by exact certified1926)
  apply certified_cons (by exact certified1926swap)
  apply certified_cons (by exact certified1927)
  apply certified_cons (by exact certified1927swap)
  apply certified_cons (by exact certified1928)
  apply certified_cons (by exact certified1928swap)
  apply certified_cons (by exact certified1929)
  apply certified_cons (by exact certified1929swap)
  apply certified_cons (by exact certified1930)
  apply certified_cons (by exact certified1930swap)
  apply certified_cons (by exact certified1931)
  apply certified_cons (by exact certified1931swap)
  apply certified_cons (by exact certified1932)
  apply certified_cons (by exact certified1932swap)
  apply certified_cons (by exact certified1933)
  apply certified_cons (by exact certified1933swap)
  apply certified_cons (by exact certified1934)
  apply certified_cons (by exact certified1934swap)
  apply certified_cons (by exact certified1935)
  apply certified_cons (by exact certified1935swap)
  apply certified_cons (by exact certified1936)
  apply certified_cons (by exact certified1936swap)
  apply certified_cons (by exact certified1937)
  apply certified_cons (by exact certified1937swap)
  apply certified_cons (by exact certified1938)
  apply certified_cons (by exact certified1938swap)
  apply certified_cons (by exact certified1939)
  apply certified_cons (by exact certified1939swap)
  apply certified_cons (by exact certified1940)
  apply certified_cons (by exact certified1940swap)
  apply certified_cons (by exact certified1941)
  apply certified_cons (by exact certified1941swap)
  apply certified_cons (by exact certified1942)
  apply certified_cons (by exact certified1942swap)
  apply certified_cons (by exact certified1943)
  apply certified_cons (by exact certified1943swap)
  apply certified_cons (by exact certified1944)
  apply certified_cons (by exact certified1944swap)
  apply certified_cons (by exact certified1945)
  apply certified_cons (by exact certified1945swap)
  apply certified_cons (by exact certified1946)
  apply certified_cons (by exact certified1946swap)
  apply certified_cons (by exact certified1947)
  apply certified_cons (by exact certified1947swap)
  apply certified_cons (by exact certified1948)
  apply certified_cons (by exact certified1948swap)
  apply certified_cons (by exact certified1949)
  apply certified_cons (by exact certified1949swap)
  simp
#print axioms certified_keys038
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
