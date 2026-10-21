/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0000
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0001
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0002
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0003
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0004
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0005
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0006
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0007
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0008
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0009
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0010
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0011
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0012
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0013
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0014
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0015
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0016
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0017
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0018
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0019
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0020
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0021
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0022
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0023
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0024
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0025
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0026
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0027
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0028
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0029
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0030
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0031
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0032
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0033
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0034
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0035
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0036
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0037
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0038
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0039
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0040
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0041
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0042
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0043
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0044
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0045
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0046
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0047
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0048
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0049
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys00 : ∀ k ∈ keys00, Certified k := by
  apply certified_cons (by exact certified0000)
  apply certified_cons (by exact certified0001)
  apply certified_cons (by exact certified0001swap)
  apply certified_cons (by exact certified0002)
  apply certified_cons (by exact certified0002swap)
  apply certified_cons (by exact certified0003)
  apply certified_cons (by exact certified0003swap)
  apply certified_cons (by exact certified0004)
  apply certified_cons (by exact certified0004swap)
  apply certified_cons (by exact certified0005)
  apply certified_cons (by exact certified0005swap)
  apply certified_cons (by exact certified0006)
  apply certified_cons (by exact certified0006swap)
  apply certified_cons (by exact certified0007)
  apply certified_cons (by exact certified0007swap)
  apply certified_cons (by exact certified0008)
  apply certified_cons (by exact certified0008swap)
  apply certified_cons (by exact certified0009)
  apply certified_cons (by exact certified0009swap)
  apply certified_cons (by exact certified0010)
  apply certified_cons (by exact certified0011)
  apply certified_cons (by exact certified0011swap)
  apply certified_cons (by exact certified0012)
  apply certified_cons (by exact certified0012swap)
  apply certified_cons (by exact certified0013)
  apply certified_cons (by exact certified0013swap)
  apply certified_cons (by exact certified0014)
  apply certified_cons (by exact certified0014swap)
  apply certified_cons (by exact certified0015)
  apply certified_cons (by exact certified0015swap)
  apply certified_cons (by exact certified0016)
  apply certified_cons (by exact certified0016swap)
  apply certified_cons (by exact certified0017)
  apply certified_cons (by exact certified0017swap)
  apply certified_cons (by exact certified0018)
  apply certified_cons (by exact certified0019)
  apply certified_cons (by exact certified0019swap)
  apply certified_cons (by exact certified0020)
  apply certified_cons (by exact certified0020swap)
  apply certified_cons (by exact certified0021)
  apply certified_cons (by exact certified0021swap)
  apply certified_cons (by exact certified0022)
  apply certified_cons (by exact certified0022swap)
  apply certified_cons (by exact certified0023)
  apply certified_cons (by exact certified0023swap)
  apply certified_cons (by exact certified0024)
  apply certified_cons (by exact certified0025)
  apply certified_cons (by exact certified0025swap)
  apply certified_cons (by exact certified0026)
  apply certified_cons (by exact certified0026swap)
  apply certified_cons (by exact certified0027)
  apply certified_cons (by exact certified0027swap)
  apply certified_cons (by exact certified0028)
  apply certified_cons (by exact certified0029)
  apply certified_cons (by exact certified0029swap)
  apply certified_cons (by exact certified0030)
  apply certified_cons (by exact certified0031)
  apply certified_cons (by exact certified0031swap)
  apply certified_cons (by exact certified0032)
  apply certified_cons (by exact certified0032swap)
  apply certified_cons (by exact certified0033)
  apply certified_cons (by exact certified0033swap)
  apply certified_cons (by exact certified0034)
  apply certified_cons (by exact certified0034swap)
  apply certified_cons (by exact certified0035)
  apply certified_cons (by exact certified0035swap)
  apply certified_cons (by exact certified0036)
  apply certified_cons (by exact certified0036swap)
  apply certified_cons (by exact certified0037)
  apply certified_cons (by exact certified0037swap)
  apply certified_cons (by exact certified0038)
  apply certified_cons (by exact certified0038swap)
  apply certified_cons (by exact certified0039)
  apply certified_cons (by exact certified0040)
  apply certified_cons (by exact certified0040swap)
  apply certified_cons (by exact certified0041)
  apply certified_cons (by exact certified0041swap)
  apply certified_cons (by exact certified0042)
  apply certified_cons (by exact certified0042swap)
  apply certified_cons (by exact certified0043)
  apply certified_cons (by exact certified0043swap)
  apply certified_cons (by exact certified0044)
  apply certified_cons (by exact certified0044swap)
  apply certified_cons (by exact certified0045)
  apply certified_cons (by exact certified0045swap)
  apply certified_cons (by exact certified0046)
  apply certified_cons (by exact certified0047)
  apply certified_cons (by exact certified0047swap)
  apply certified_cons (by exact certified0048)
  apply certified_cons (by exact certified0048swap)
  apply certified_cons (by exact certified0049)
  apply certified_cons (by exact certified0049swap)
  simp
#print axioms certified_keys00
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
