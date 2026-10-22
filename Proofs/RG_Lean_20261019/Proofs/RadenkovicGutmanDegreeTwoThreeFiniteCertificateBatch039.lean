/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1950
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1951
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1952
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1953
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1954
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1955
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1956
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1957
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1958
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1959
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1960
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1961
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1962
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1963
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1964
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1965
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1966
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1967
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1968
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1969
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1970
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1971
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1972
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1973
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1974
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1975
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1976
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1977
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1978
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1979
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1980
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1981
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1982
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1983
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1984
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1985
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1986
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1987
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1988
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1989
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1990
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1991
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1992
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1993
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1994
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1995
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1996
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1997
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1998
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase1999
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys039 : ∀ k ∈ keys039, Certified k := by
  apply certified_cons (by exact certified1950)
  apply certified_cons (by exact certified1950swap)
  apply certified_cons (by exact certified1951)
  apply certified_cons (by exact certified1951swap)
  apply certified_cons (by exact certified1952)
  apply certified_cons (by exact certified1952swap)
  apply certified_cons (by exact certified1953)
  apply certified_cons (by exact certified1953swap)
  apply certified_cons (by exact certified1954)
  apply certified_cons (by exact certified1954swap)
  apply certified_cons (by exact certified1955)
  apply certified_cons (by exact certified1955swap)
  apply certified_cons (by exact certified1956)
  apply certified_cons (by exact certified1956swap)
  apply certified_cons (by exact certified1957)
  apply certified_cons (by exact certified1957swap)
  apply certified_cons (by exact certified1958)
  apply certified_cons (by exact certified1958swap)
  apply certified_cons (by exact certified1959)
  apply certified_cons (by exact certified1959swap)
  apply certified_cons (by exact certified1960)
  apply certified_cons (by exact certified1960swap)
  apply certified_cons (by exact certified1961)
  apply certified_cons (by exact certified1961swap)
  apply certified_cons (by exact certified1962)
  apply certified_cons (by exact certified1962swap)
  apply certified_cons (by exact certified1963)
  apply certified_cons (by exact certified1963swap)
  apply certified_cons (by exact certified1964)
  apply certified_cons (by exact certified1964swap)
  apply certified_cons (by exact certified1965)
  apply certified_cons (by exact certified1965swap)
  apply certified_cons (by exact certified1966)
  apply certified_cons (by exact certified1966swap)
  apply certified_cons (by exact certified1967)
  apply certified_cons (by exact certified1967swap)
  apply certified_cons (by exact certified1968)
  apply certified_cons (by exact certified1968swap)
  apply certified_cons (by exact certified1969)
  apply certified_cons (by exact certified1969swap)
  apply certified_cons (by exact certified1970)
  apply certified_cons (by exact certified1970swap)
  apply certified_cons (by exact certified1971)
  apply certified_cons (by exact certified1971swap)
  apply certified_cons (by exact certified1972)
  apply certified_cons (by exact certified1972swap)
  apply certified_cons (by exact certified1973)
  apply certified_cons (by exact certified1973swap)
  apply certified_cons (by exact certified1974)
  apply certified_cons (by exact certified1974swap)
  apply certified_cons (by exact certified1975)
  apply certified_cons (by exact certified1975swap)
  apply certified_cons (by exact certified1976)
  apply certified_cons (by exact certified1976swap)
  apply certified_cons (by exact certified1977)
  apply certified_cons (by exact certified1977swap)
  apply certified_cons (by exact certified1978)
  apply certified_cons (by exact certified1978swap)
  apply certified_cons (by exact certified1979)
  apply certified_cons (by exact certified1979swap)
  apply certified_cons (by exact certified1980)
  apply certified_cons (by exact certified1980swap)
  apply certified_cons (by exact certified1981)
  apply certified_cons (by exact certified1981swap)
  apply certified_cons (by exact certified1982)
  apply certified_cons (by exact certified1982swap)
  apply certified_cons (by exact certified1983)
  apply certified_cons (by exact certified1983swap)
  apply certified_cons (by exact certified1984)
  apply certified_cons (by exact certified1984swap)
  apply certified_cons (by exact certified1985)
  apply certified_cons (by exact certified1985swap)
  apply certified_cons (by exact certified1986)
  apply certified_cons (by exact certified1986swap)
  apply certified_cons (by exact certified1987)
  apply certified_cons (by exact certified1987swap)
  apply certified_cons (by exact certified1988)
  apply certified_cons (by exact certified1988swap)
  apply certified_cons (by exact certified1989)
  apply certified_cons (by exact certified1989swap)
  apply certified_cons (by exact certified1990)
  apply certified_cons (by exact certified1990swap)
  apply certified_cons (by exact certified1991)
  apply certified_cons (by exact certified1991swap)
  apply certified_cons (by exact certified1992)
  apply certified_cons (by exact certified1992swap)
  apply certified_cons (by exact certified1993)
  apply certified_cons (by exact certified1993swap)
  apply certified_cons (by exact certified1994)
  apply certified_cons (by exact certified1994swap)
  apply certified_cons (by exact certified1995)
  apply certified_cons (by exact certified1995swap)
  apply certified_cons (by exact certified1996)
  apply certified_cons (by exact certified1996swap)
  apply certified_cons (by exact certified1997)
  apply certified_cons (by exact certified1997swap)
  apply certified_cons (by exact certified1998)
  apply certified_cons (by exact certified1998swap)
  apply certified_cons (by exact certified1999)
  apply certified_cons (by exact certified1999swap)
  simp
#print axioms certified_keys039
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
