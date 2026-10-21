/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2100
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2101
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2102
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2103
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2104
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2105
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2106
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2107
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2108
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2109
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2110
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2111
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2112
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2113
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2114
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2115
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2116
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2117
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2118
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2119
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2120
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2121
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2122
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2123
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2124
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2125
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2126
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2127
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2128
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2129
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2130
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2131
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2132
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2133
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2134
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2135
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2136
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2137
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2138
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2139
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2140
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2141
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2142
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2143
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2144
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2145
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2146
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2147
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2148
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2149
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys42 : ∀ k ∈ keys42, Certified k := by
  apply certified_cons (by exact certified2100)
  apply certified_cons (by exact certified2101)
  apply certified_cons (by exact certified2102)
  apply certified_cons (by exact certified2103)
  apply certified_cons (by exact certified2104)
  apply certified_cons (by exact certified2105)
  apply certified_cons (by exact certified2106)
  apply certified_cons (by exact certified2107)
  apply certified_cons (by exact certified2108)
  apply certified_cons (by exact certified2109)
  apply certified_cons (by exact certified2110)
  apply certified_cons (by exact certified2111)
  apply certified_cons (by exact certified2112)
  apply certified_cons (by exact certified2113)
  apply certified_cons (by exact certified2114)
  apply certified_cons (by exact certified2115)
  apply certified_cons (by exact certified2116)
  apply certified_cons (by exact certified2117)
  apply certified_cons (by exact certified2118)
  apply certified_cons (by exact certified2119)
  apply certified_cons (by exact certified2120)
  apply certified_cons (by exact certified2121)
  apply certified_cons (by exact certified2122)
  apply certified_cons (by exact certified2123)
  apply certified_cons (by exact certified2124)
  apply certified_cons (by exact certified2125)
  apply certified_cons (by exact certified2126)
  apply certified_cons (by exact certified2127)
  apply certified_cons (by exact certified2128)
  apply certified_cons (by exact certified2129)
  apply certified_cons (by exact certified2130)
  apply certified_cons (by exact certified2131)
  apply certified_cons (by exact certified2132)
  apply certified_cons (by exact certified2133)
  apply certified_cons (by exact certified2134)
  apply certified_cons (by exact certified2135)
  apply certified_cons (by exact certified2136)
  apply certified_cons (by exact certified2137)
  apply certified_cons (by exact certified2138)
  apply certified_cons (by exact certified2139)
  apply certified_cons (by exact certified2140)
  apply certified_cons (by exact certified2141)
  apply certified_cons (by exact certified2142)
  apply certified_cons (by exact certified2143)
  apply certified_cons (by exact certified2144)
  apply certified_cons (by exact certified2145)
  apply certified_cons (by exact certified2146)
  apply certified_cons (by exact certified2147)
  apply certified_cons (by exact certified2148)
  apply certified_cons (by exact certified2149)
  simp
#print axioms certified_keys42
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
