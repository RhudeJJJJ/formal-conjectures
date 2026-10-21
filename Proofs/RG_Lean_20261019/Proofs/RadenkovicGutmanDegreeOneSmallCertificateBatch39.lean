/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1950
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1951
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1952
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1953
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1954
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1955
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1956
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1957
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1958
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1959
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1960
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1961
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1962
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1963
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1964
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1965
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1966
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1967
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1968
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1969
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1970
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1971
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1972
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1973
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1974
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1975
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1976
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1977
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1978
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1979
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1980
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1981
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1982
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1983
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1984
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1985
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1986
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1987
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1988
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1989
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1990
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1991
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1992
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1993
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1994
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1995
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1996
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1997
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1998
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase1999
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys39 : ∀ k ∈ keys39, Certified k := by
  apply certified_cons (by exact certified1950)
  apply certified_cons (by exact certified1951)
  apply certified_cons (by exact certified1952)
  apply certified_cons (by exact certified1953)
  apply certified_cons (by exact certified1954)
  apply certified_cons (by exact certified1955)
  apply certified_cons (by exact certified1956)
  apply certified_cons (by exact certified1957)
  apply certified_cons (by exact certified1958)
  apply certified_cons (by exact certified1959)
  apply certified_cons (by exact certified1960)
  apply certified_cons (by exact certified1961)
  apply certified_cons (by exact certified1962)
  apply certified_cons (by exact certified1963)
  apply certified_cons (by exact certified1964)
  apply certified_cons (by exact certified1965)
  apply certified_cons (by exact certified1966)
  apply certified_cons (by exact certified1967)
  apply certified_cons (by exact certified1968)
  apply certified_cons (by exact certified1969)
  apply certified_cons (by exact certified1970)
  apply certified_cons (by exact certified1971)
  apply certified_cons (by exact certified1972)
  apply certified_cons (by exact certified1973)
  apply certified_cons (by exact certified1974)
  apply certified_cons (by exact certified1975)
  apply certified_cons (by exact certified1976)
  apply certified_cons (by exact certified1977)
  apply certified_cons (by exact certified1978)
  apply certified_cons (by exact certified1979)
  apply certified_cons (by exact certified1980)
  apply certified_cons (by exact certified1981)
  apply certified_cons (by exact certified1982)
  apply certified_cons (by exact certified1983)
  apply certified_cons (by exact certified1984)
  apply certified_cons (by exact certified1985)
  apply certified_cons (by exact certified1986)
  apply certified_cons (by exact certified1987)
  apply certified_cons (by exact certified1988)
  apply certified_cons (by exact certified1989)
  apply certified_cons (by exact certified1990)
  apply certified_cons (by exact certified1991)
  apply certified_cons (by exact certified1992)
  apply certified_cons (by exact certified1993)
  apply certified_cons (by exact certified1994)
  apply certified_cons (by exact certified1995)
  apply certified_cons (by exact certified1996)
  apply certified_cons (by exact certified1997)
  apply certified_cons (by exact certified1998)
  apply certified_cons (by exact certified1999)
  simp
#print axioms certified_keys39
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
