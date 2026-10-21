/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2000
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2001
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2002
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2003
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2004
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2005
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2006
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2007
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2008
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2009
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2010
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2011
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2012
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2013
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2014
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2015
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2016
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2017
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2018
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2019
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2020
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2021
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2022
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2023
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2024
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2025
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2026
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2027
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2028
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2029
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2030
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2031
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2032
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2033
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2034
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2035
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2036
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2037
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2038
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2039
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2040
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2041
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2042
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2043
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2044
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2045
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2046
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2047
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2048
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2049
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys40 : ∀ k ∈ keys40, Certified k := by
  apply certified_cons (by exact certified2000)
  apply certified_cons (by exact certified2001)
  apply certified_cons (by exact certified2002)
  apply certified_cons (by exact certified2003)
  apply certified_cons (by exact certified2004)
  apply certified_cons (by exact certified2005)
  apply certified_cons (by exact certified2006)
  apply certified_cons (by exact certified2007)
  apply certified_cons (by exact certified2008)
  apply certified_cons (by exact certified2009)
  apply certified_cons (by exact certified2010)
  apply certified_cons (by exact certified2011)
  apply certified_cons (by exact certified2012)
  apply certified_cons (by exact certified2013)
  apply certified_cons (by exact certified2014)
  apply certified_cons (by exact certified2015)
  apply certified_cons (by exact certified2016)
  apply certified_cons (by exact certified2017)
  apply certified_cons (by exact certified2018)
  apply certified_cons (by exact certified2019)
  apply certified_cons (by exact certified2020)
  apply certified_cons (by exact certified2021)
  apply certified_cons (by exact certified2022)
  apply certified_cons (by exact certified2023)
  apply certified_cons (by exact certified2024)
  apply certified_cons (by exact certified2025)
  apply certified_cons (by exact certified2026)
  apply certified_cons (by exact certified2027)
  apply certified_cons (by exact certified2028)
  apply certified_cons (by exact certified2029)
  apply certified_cons (by exact certified2030)
  apply certified_cons (by exact certified2031)
  apply certified_cons (by exact certified2032)
  apply certified_cons (by exact certified2033)
  apply certified_cons (by exact certified2034)
  apply certified_cons (by exact certified2035)
  apply certified_cons (by exact certified2036)
  apply certified_cons (by exact certified2037)
  apply certified_cons (by exact certified2038)
  apply certified_cons (by exact certified2039)
  apply certified_cons (by exact certified2040)
  apply certified_cons (by exact certified2041)
  apply certified_cons (by exact certified2042)
  apply certified_cons (by exact certified2043)
  apply certified_cons (by exact certified2044)
  apply certified_cons (by exact certified2045)
  apply certified_cons (by exact certified2046)
  apply certified_cons (by exact certified2047)
  apply certified_cons (by exact certified2048)
  apply certified_cons (by exact certified2049)
  simp
#print axioms certified_keys40
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
