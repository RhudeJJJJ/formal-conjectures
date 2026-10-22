/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4000
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4001
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4002
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4003
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4004
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4005
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4006
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4007
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4008
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4009
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4010
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4011
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4012
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4013
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4014
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4015
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4016
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4017
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4018
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4019
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4020
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4021
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4022
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4023
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4024
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4025
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4026
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4027
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4028
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4029
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4030
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4031
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4032
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4033
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4034
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4035
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4036
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4037
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4038
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4039
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4040
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4041
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4042
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4043
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4044
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4045
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4046
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4047
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4048
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase4049
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys080 : ∀ k ∈ keys080, Certified k := by
  apply certified_cons (by exact certified4000)
  apply certified_cons (by exact certified4000swap)
  apply certified_cons (by exact certified4001)
  apply certified_cons (by exact certified4001swap)
  apply certified_cons (by exact certified4002)
  apply certified_cons (by exact certified4002swap)
  apply certified_cons (by exact certified4003)
  apply certified_cons (by exact certified4003swap)
  apply certified_cons (by exact certified4004)
  apply certified_cons (by exact certified4004swap)
  apply certified_cons (by exact certified4005)
  apply certified_cons (by exact certified4005swap)
  apply certified_cons (by exact certified4006)
  apply certified_cons (by exact certified4006swap)
  apply certified_cons (by exact certified4007)
  apply certified_cons (by exact certified4007swap)
  apply certified_cons (by exact certified4008)
  apply certified_cons (by exact certified4008swap)
  apply certified_cons (by exact certified4009)
  apply certified_cons (by exact certified4009swap)
  apply certified_cons (by exact certified4010)
  apply certified_cons (by exact certified4010swap)
  apply certified_cons (by exact certified4011)
  apply certified_cons (by exact certified4011swap)
  apply certified_cons (by exact certified4012)
  apply certified_cons (by exact certified4012swap)
  apply certified_cons (by exact certified4013)
  apply certified_cons (by exact certified4013swap)
  apply certified_cons (by exact certified4014)
  apply certified_cons (by exact certified4014swap)
  apply certified_cons (by exact certified4015)
  apply certified_cons (by exact certified4015swap)
  apply certified_cons (by exact certified4016)
  apply certified_cons (by exact certified4016swap)
  apply certified_cons (by exact certified4017)
  apply certified_cons (by exact certified4017swap)
  apply certified_cons (by exact certified4018)
  apply certified_cons (by exact certified4018swap)
  apply certified_cons (by exact certified4019)
  apply certified_cons (by exact certified4019swap)
  apply certified_cons (by exact certified4020)
  apply certified_cons (by exact certified4020swap)
  apply certified_cons (by exact certified4021)
  apply certified_cons (by exact certified4021swap)
  apply certified_cons (by exact certified4022)
  apply certified_cons (by exact certified4022swap)
  apply certified_cons (by exact certified4023)
  apply certified_cons (by exact certified4023swap)
  apply certified_cons (by exact certified4024)
  apply certified_cons (by exact certified4024swap)
  apply certified_cons (by exact certified4025)
  apply certified_cons (by exact certified4025swap)
  apply certified_cons (by exact certified4026)
  apply certified_cons (by exact certified4026swap)
  apply certified_cons (by exact certified4027)
  apply certified_cons (by exact certified4027swap)
  apply certified_cons (by exact certified4028)
  apply certified_cons (by exact certified4028swap)
  apply certified_cons (by exact certified4029)
  apply certified_cons (by exact certified4029swap)
  apply certified_cons (by exact certified4030)
  apply certified_cons (by exact certified4030swap)
  apply certified_cons (by exact certified4031)
  apply certified_cons (by exact certified4031swap)
  apply certified_cons (by exact certified4032)
  apply certified_cons (by exact certified4032swap)
  apply certified_cons (by exact certified4033)
  apply certified_cons (by exact certified4034)
  apply certified_cons (by exact certified4035)
  apply certified_cons (by exact certified4036)
  apply certified_cons (by exact certified4037)
  apply certified_cons (by exact certified4038)
  apply certified_cons (by exact certified4039)
  apply certified_cons (by exact certified4040)
  apply certified_cons (by exact certified4041)
  apply certified_cons (by exact certified4042)
  apply certified_cons (by exact certified4043)
  apply certified_cons (by exact certified4044)
  apply certified_cons (by exact certified4045)
  apply certified_cons (by exact certified4046)
  apply certified_cons (by exact certified4047)
  apply certified_cons (by exact certified4048)
  apply certified_cons (by exact certified4049)
  simp
#print axioms certified_keys080
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
