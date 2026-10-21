/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0000
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0001
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0002
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0003
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0004
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0005
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0006
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0007
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0008
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0009
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0010
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0011
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0012
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0013
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0014
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0015
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0016
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0017
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0018
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0019
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0020
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0021
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0022
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0023
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0024
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0025
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0026
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0027
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0028
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0029
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0030
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0031
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0032
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0033
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0034
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0035
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0036
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0037
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0038
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0039
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0040
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0041
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0042
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0043
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0044
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0045
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0046
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0047
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0048
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0049
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys000 : ∀ k ∈ keys000, Certified k := by
  apply certified_cons (by exact certified0000)
  apply certified_cons (by exact certified0001)
  apply certified_cons (by exact certified0002)
  apply certified_cons (by exact certified0003)
  apply certified_cons (by exact certified0004)
  apply certified_cons (by exact certified0005)
  apply certified_cons (by exact certified0006)
  apply certified_cons (by exact certified0007)
  apply certified_cons (by exact certified0008)
  apply certified_cons (by exact certified0009)
  apply certified_cons (by exact certified0010)
  apply certified_cons (by exact certified0011)
  apply certified_cons (by exact certified0012)
  apply certified_cons (by exact certified0013)
  apply certified_cons (by exact certified0014)
  apply certified_cons (by exact certified0015)
  apply certified_cons (by exact certified0016)
  apply certified_cons (by exact certified0017)
  apply certified_cons (by exact certified0018)
  apply certified_cons (by exact certified0019)
  apply certified_cons (by exact certified0020)
  apply certified_cons (by exact certified0021)
  apply certified_cons (by exact certified0022)
  apply certified_cons (by exact certified0023)
  apply certified_cons (by exact certified0024)
  apply certified_cons (by exact certified0025)
  apply certified_cons (by exact certified0026)
  apply certified_cons (by exact certified0027)
  apply certified_cons (by exact certified0028)
  apply certified_cons (by exact certified0029)
  apply certified_cons (by exact certified0030)
  apply certified_cons (by exact certified0031)
  apply certified_cons (by exact certified0032)
  apply certified_cons (by exact certified0033)
  apply certified_cons (by exact certified0034)
  apply certified_cons (by exact certified0035)
  apply certified_cons (by exact certified0036)
  apply certified_cons (by exact certified0037)
  apply certified_cons (by exact certified0038)
  apply certified_cons (by exact certified0039)
  apply certified_cons (by exact certified0040)
  apply certified_cons (by exact certified0041)
  apply certified_cons (by exact certified0042)
  apply certified_cons (by exact certified0043)
  apply certified_cons (by exact certified0044)
  apply certified_cons (by exact certified0045)
  apply certified_cons (by exact certified0046)
  apply certified_cons (by exact certified0047)
  apply certified_cons (by exact certified0048)
  apply certified_cons (by exact certified0049)
  simp
#print axioms certified_keys000
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
