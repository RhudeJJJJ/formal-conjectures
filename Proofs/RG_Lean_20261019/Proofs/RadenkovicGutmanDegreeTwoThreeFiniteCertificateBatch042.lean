/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2100
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2101
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2102
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2103
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2104
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2105
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2106
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2107
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2108
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2109
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2110
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2111
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2112
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2113
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2114
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2115
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2116
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2117
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2118
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2119
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2120
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2121
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2122
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2123
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2124
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2125
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2126
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2127
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2128
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2129
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2130
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2131
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2132
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2133
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2134
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2135
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2136
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2137
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2138
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2139
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2140
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2141
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2142
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2143
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2144
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2145
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2146
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2147
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2148
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase2149
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys042 : ∀ k ∈ keys042, Certified k := by
  apply certified_cons (by exact certified2100)
  apply certified_cons (by exact certified2100swap)
  apply certified_cons (by exact certified2101)
  apply certified_cons (by exact certified2101swap)
  apply certified_cons (by exact certified2102)
  apply certified_cons (by exact certified2102swap)
  apply certified_cons (by exact certified2103)
  apply certified_cons (by exact certified2103swap)
  apply certified_cons (by exact certified2104)
  apply certified_cons (by exact certified2104swap)
  apply certified_cons (by exact certified2105)
  apply certified_cons (by exact certified2105swap)
  apply certified_cons (by exact certified2106)
  apply certified_cons (by exact certified2106swap)
  apply certified_cons (by exact certified2107)
  apply certified_cons (by exact certified2107swap)
  apply certified_cons (by exact certified2108)
  apply certified_cons (by exact certified2108swap)
  apply certified_cons (by exact certified2109)
  apply certified_cons (by exact certified2109swap)
  apply certified_cons (by exact certified2110)
  apply certified_cons (by exact certified2110swap)
  apply certified_cons (by exact certified2111)
  apply certified_cons (by exact certified2111swap)
  apply certified_cons (by exact certified2112)
  apply certified_cons (by exact certified2112swap)
  apply certified_cons (by exact certified2113)
  apply certified_cons (by exact certified2113swap)
  apply certified_cons (by exact certified2114)
  apply certified_cons (by exact certified2114swap)
  apply certified_cons (by exact certified2115)
  apply certified_cons (by exact certified2115swap)
  apply certified_cons (by exact certified2116)
  apply certified_cons (by exact certified2116swap)
  apply certified_cons (by exact certified2117)
  apply certified_cons (by exact certified2117swap)
  apply certified_cons (by exact certified2118)
  apply certified_cons (by exact certified2118swap)
  apply certified_cons (by exact certified2119)
  apply certified_cons (by exact certified2119swap)
  apply certified_cons (by exact certified2120)
  apply certified_cons (by exact certified2120swap)
  apply certified_cons (by exact certified2121)
  apply certified_cons (by exact certified2121swap)
  apply certified_cons (by exact certified2122)
  apply certified_cons (by exact certified2122swap)
  apply certified_cons (by exact certified2123)
  apply certified_cons (by exact certified2123swap)
  apply certified_cons (by exact certified2124)
  apply certified_cons (by exact certified2124swap)
  apply certified_cons (by exact certified2125)
  apply certified_cons (by exact certified2125swap)
  apply certified_cons (by exact certified2126)
  apply certified_cons (by exact certified2126swap)
  apply certified_cons (by exact certified2127)
  apply certified_cons (by exact certified2127swap)
  apply certified_cons (by exact certified2128)
  apply certified_cons (by exact certified2128swap)
  apply certified_cons (by exact certified2129)
  apply certified_cons (by exact certified2129swap)
  apply certified_cons (by exact certified2130)
  apply certified_cons (by exact certified2130swap)
  apply certified_cons (by exact certified2131)
  apply certified_cons (by exact certified2131swap)
  apply certified_cons (by exact certified2132)
  apply certified_cons (by exact certified2132swap)
  apply certified_cons (by exact certified2133)
  apply certified_cons (by exact certified2133swap)
  apply certified_cons (by exact certified2134)
  apply certified_cons (by exact certified2134swap)
  apply certified_cons (by exact certified2135)
  apply certified_cons (by exact certified2135swap)
  apply certified_cons (by exact certified2136)
  apply certified_cons (by exact certified2136swap)
  apply certified_cons (by exact certified2137)
  apply certified_cons (by exact certified2137swap)
  apply certified_cons (by exact certified2138)
  apply certified_cons (by exact certified2138swap)
  apply certified_cons (by exact certified2139)
  apply certified_cons (by exact certified2139swap)
  apply certified_cons (by exact certified2140)
  apply certified_cons (by exact certified2140swap)
  apply certified_cons (by exact certified2141)
  apply certified_cons (by exact certified2141swap)
  apply certified_cons (by exact certified2142)
  apply certified_cons (by exact certified2142swap)
  apply certified_cons (by exact certified2143)
  apply certified_cons (by exact certified2143swap)
  apply certified_cons (by exact certified2144)
  apply certified_cons (by exact certified2144swap)
  apply certified_cons (by exact certified2145)
  apply certified_cons (by exact certified2145swap)
  apply certified_cons (by exact certified2146)
  apply certified_cons (by exact certified2146swap)
  apply certified_cons (by exact certified2147)
  apply certified_cons (by exact certified2147swap)
  apply certified_cons (by exact certified2148)
  apply certified_cons (by exact certified2148swap)
  apply certified_cons (by exact certified2149)
  apply certified_cons (by exact certified2149swap)
  simp
#print axioms certified_keys042
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
