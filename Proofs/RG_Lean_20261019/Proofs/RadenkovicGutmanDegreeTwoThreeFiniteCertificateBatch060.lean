/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3000
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3001
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3002
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3003
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3004
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3005
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3006
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3007
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3008
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3009
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3010
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3011
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3012
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3013
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3014
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3015
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3016
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3017
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3018
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3019
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3020
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3021
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3022
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3023
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3024
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3025
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3026
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3027
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3028
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3029
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3030
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3031
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3032
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3033
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3034
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3035
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3036
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3037
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3038
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3039
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3040
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3041
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3042
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3043
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3044
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3045
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3046
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3047
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3048
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3049
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys060 : ∀ k ∈ keys060, Certified k := by
  apply certified_cons (by exact certified3000)
  apply certified_cons (by exact certified3000swap)
  apply certified_cons (by exact certified3001)
  apply certified_cons (by exact certified3001swap)
  apply certified_cons (by exact certified3002)
  apply certified_cons (by exact certified3002swap)
  apply certified_cons (by exact certified3003)
  apply certified_cons (by exact certified3003swap)
  apply certified_cons (by exact certified3004)
  apply certified_cons (by exact certified3004swap)
  apply certified_cons (by exact certified3005)
  apply certified_cons (by exact certified3005swap)
  apply certified_cons (by exact certified3006)
  apply certified_cons (by exact certified3006swap)
  apply certified_cons (by exact certified3007)
  apply certified_cons (by exact certified3007swap)
  apply certified_cons (by exact certified3008)
  apply certified_cons (by exact certified3008swap)
  apply certified_cons (by exact certified3009)
  apply certified_cons (by exact certified3009swap)
  apply certified_cons (by exact certified3010)
  apply certified_cons (by exact certified3010swap)
  apply certified_cons (by exact certified3011)
  apply certified_cons (by exact certified3011swap)
  apply certified_cons (by exact certified3012)
  apply certified_cons (by exact certified3012swap)
  apply certified_cons (by exact certified3013)
  apply certified_cons (by exact certified3013swap)
  apply certified_cons (by exact certified3014)
  apply certified_cons (by exact certified3014swap)
  apply certified_cons (by exact certified3015)
  apply certified_cons (by exact certified3015swap)
  apply certified_cons (by exact certified3016)
  apply certified_cons (by exact certified3016swap)
  apply certified_cons (by exact certified3017)
  apply certified_cons (by exact certified3017swap)
  apply certified_cons (by exact certified3018)
  apply certified_cons (by exact certified3018swap)
  apply certified_cons (by exact certified3019)
  apply certified_cons (by exact certified3019swap)
  apply certified_cons (by exact certified3020)
  apply certified_cons (by exact certified3020swap)
  apply certified_cons (by exact certified3021)
  apply certified_cons (by exact certified3021swap)
  apply certified_cons (by exact certified3022)
  apply certified_cons (by exact certified3022swap)
  apply certified_cons (by exact certified3023)
  apply certified_cons (by exact certified3023swap)
  apply certified_cons (by exact certified3024)
  apply certified_cons (by exact certified3024swap)
  apply certified_cons (by exact certified3025)
  apply certified_cons (by exact certified3025swap)
  apply certified_cons (by exact certified3026)
  apply certified_cons (by exact certified3026swap)
  apply certified_cons (by exact certified3027)
  apply certified_cons (by exact certified3027swap)
  apply certified_cons (by exact certified3028)
  apply certified_cons (by exact certified3028swap)
  apply certified_cons (by exact certified3029)
  apply certified_cons (by exact certified3029swap)
  apply certified_cons (by exact certified3030)
  apply certified_cons (by exact certified3030swap)
  apply certified_cons (by exact certified3031)
  apply certified_cons (by exact certified3031swap)
  apply certified_cons (by exact certified3032)
  apply certified_cons (by exact certified3032swap)
  apply certified_cons (by exact certified3033)
  apply certified_cons (by exact certified3033swap)
  apply certified_cons (by exact certified3034)
  apply certified_cons (by exact certified3034swap)
  apply certified_cons (by exact certified3035)
  apply certified_cons (by exact certified3035swap)
  apply certified_cons (by exact certified3036)
  apply certified_cons (by exact certified3036swap)
  apply certified_cons (by exact certified3037)
  apply certified_cons (by exact certified3037swap)
  apply certified_cons (by exact certified3038)
  apply certified_cons (by exact certified3038swap)
  apply certified_cons (by exact certified3039)
  apply certified_cons (by exact certified3039swap)
  apply certified_cons (by exact certified3040)
  apply certified_cons (by exact certified3040swap)
  apply certified_cons (by exact certified3041)
  apply certified_cons (by exact certified3041swap)
  apply certified_cons (by exact certified3042)
  apply certified_cons (by exact certified3042swap)
  apply certified_cons (by exact certified3043)
  apply certified_cons (by exact certified3043swap)
  apply certified_cons (by exact certified3044)
  apply certified_cons (by exact certified3044swap)
  apply certified_cons (by exact certified3045)
  apply certified_cons (by exact certified3045swap)
  apply certified_cons (by exact certified3046)
  apply certified_cons (by exact certified3046swap)
  apply certified_cons (by exact certified3047)
  apply certified_cons (by exact certified3047swap)
  apply certified_cons (by exact certified3048)
  apply certified_cons (by exact certified3048swap)
  apply certified_cons (by exact certified3049)
  apply certified_cons (by exact certified3049swap)
  simp
#print axioms certified_keys060
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
