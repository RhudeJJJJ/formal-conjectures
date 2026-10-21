/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2150
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2151
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2152
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2153
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2154
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2155
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2156
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2157
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2158
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2159
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2160
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2161
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2162
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2163
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2164
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2165
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2166
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2167
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2168
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2169
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2170
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2171
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2172
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2173
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2174
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2175
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2176
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2177
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2178
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2179
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2180
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2181
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2182
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2183
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2184
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2185
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2186
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2187
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2188
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2189
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2190
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2191
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2192
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2193
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2194
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2195
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2196
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2197
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2198
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase2199
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys43 : ∀ k ∈ keys43, Certified k := by
  apply certified_cons (by exact certified2150)
  apply certified_cons (by exact certified2151)
  apply certified_cons (by exact certified2152)
  apply certified_cons (by exact certified2153)
  apply certified_cons (by exact certified2154)
  apply certified_cons (by exact certified2155)
  apply certified_cons (by exact certified2156)
  apply certified_cons (by exact certified2157)
  apply certified_cons (by exact certified2158)
  apply certified_cons (by exact certified2159)
  apply certified_cons (by exact certified2160)
  apply certified_cons (by exact certified2161)
  apply certified_cons (by exact certified2162)
  apply certified_cons (by exact certified2163)
  apply certified_cons (by exact certified2164)
  apply certified_cons (by exact certified2165)
  apply certified_cons (by exact certified2166)
  apply certified_cons (by exact certified2167)
  apply certified_cons (by exact certified2168)
  apply certified_cons (by exact certified2169)
  apply certified_cons (by exact certified2170)
  apply certified_cons (by exact certified2171)
  apply certified_cons (by exact certified2172)
  apply certified_cons (by exact certified2173)
  apply certified_cons (by exact certified2174)
  apply certified_cons (by exact certified2175)
  apply certified_cons (by exact certified2176)
  apply certified_cons (by exact certified2177)
  apply certified_cons (by exact certified2178)
  apply certified_cons (by exact certified2179)
  apply certified_cons (by exact certified2180)
  apply certified_cons (by exact certified2181)
  apply certified_cons (by exact certified2182)
  apply certified_cons (by exact certified2183)
  apply certified_cons (by exact certified2184)
  apply certified_cons (by exact certified2185)
  apply certified_cons (by exact certified2186)
  apply certified_cons (by exact certified2187)
  apply certified_cons (by exact certified2188)
  apply certified_cons (by exact certified2189)
  apply certified_cons (by exact certified2190)
  apply certified_cons (by exact certified2191)
  apply certified_cons (by exact certified2192)
  apply certified_cons (by exact certified2193)
  apply certified_cons (by exact certified2194)
  apply certified_cons (by exact certified2195)
  apply certified_cons (by exact certified2196)
  apply certified_cons (by exact certified2197)
  apply certified_cons (by exact certified2198)
  apply certified_cons (by exact certified2199)
  simp
#print axioms certified_keys43
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
