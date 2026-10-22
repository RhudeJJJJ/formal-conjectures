/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0150
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0151
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0152
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0153
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0154
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0155
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0156
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0157
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0158
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0159
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0160
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0161
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0162
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0163
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0164
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0165
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0166
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0167
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0168
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0169
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0170
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0171
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0172
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0173
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0174
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0175
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0176
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0177
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0178
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0179
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0180
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0181
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0182
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0183
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0184
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0185
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0186
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0187
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0188
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0189
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0190
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0191
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0192
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0193
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0194
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0195
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0196
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0197
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0198
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0199
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys003 : ∀ k ∈ keys003, Certified k := by
  apply certified_cons (by exact certified0150)
  apply certified_cons (by exact certified0151)
  apply certified_cons (by exact certified0152)
  apply certified_cons (by exact certified0153)
  apply certified_cons (by exact certified0154)
  apply certified_cons (by exact certified0155)
  apply certified_cons (by exact certified0156)
  apply certified_cons (by exact certified0157)
  apply certified_cons (by exact certified0158)
  apply certified_cons (by exact certified0159)
  apply certified_cons (by exact certified0160)
  apply certified_cons (by exact certified0161)
  apply certified_cons (by exact certified0162)
  apply certified_cons (by exact certified0163)
  apply certified_cons (by exact certified0164)
  apply certified_cons (by exact certified0165)
  apply certified_cons (by exact certified0166)
  apply certified_cons (by exact certified0167)
  apply certified_cons (by exact certified0168)
  apply certified_cons (by exact certified0169)
  apply certified_cons (by exact certified0170)
  apply certified_cons (by exact certified0171)
  apply certified_cons (by exact certified0172)
  apply certified_cons (by exact certified0173)
  apply certified_cons (by exact certified0174)
  apply certified_cons (by exact certified0175)
  apply certified_cons (by exact certified0176)
  apply certified_cons (by exact certified0177)
  apply certified_cons (by exact certified0178)
  apply certified_cons (by exact certified0179)
  apply certified_cons (by exact certified0180)
  apply certified_cons (by exact certified0181)
  apply certified_cons (by exact certified0182)
  apply certified_cons (by exact certified0183)
  apply certified_cons (by exact certified0184)
  apply certified_cons (by exact certified0185)
  apply certified_cons (by exact certified0186)
  apply certified_cons (by exact certified0187)
  apply certified_cons (by exact certified0188)
  apply certified_cons (by exact certified0189)
  apply certified_cons (by exact certified0190)
  apply certified_cons (by exact certified0191)
  apply certified_cons (by exact certified0192)
  apply certified_cons (by exact certified0193)
  apply certified_cons (by exact certified0194)
  apply certified_cons (by exact certified0195)
  apply certified_cons (by exact certified0196)
  apply certified_cons (by exact certified0197)
  apply certified_cons (by exact certified0198)
  apply certified_cons (by exact certified0199)
  simp
#print axioms certified_keys003
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
