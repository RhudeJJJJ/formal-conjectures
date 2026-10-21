/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0150
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0151
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0152
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0153
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0154
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0155
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0156
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0157
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0158
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0159
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0160
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0161
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0162
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0163
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0164
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0165
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0166
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0167
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0168
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0169
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0170
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0171
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0172
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0173
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0174
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0175
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0176
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0177
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0178
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0179
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0180
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0181
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0182
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0183
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0184
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0185
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0186
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0187
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0188
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0189
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0190
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0191
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0192
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0193
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0194
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0195
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0196
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0197
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0198
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0199
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys03 : ∀ k ∈ keys03, Certified k := by
  apply certified_cons (by exact certified0150)
  apply certified_cons (by exact certified0151)
  apply certified_cons (by exact certified0151swap)
  apply certified_cons (by exact certified0152)
  apply certified_cons (by exact certified0152swap)
  apply certified_cons (by exact certified0153)
  apply certified_cons (by exact certified0153swap)
  apply certified_cons (by exact certified0154)
  apply certified_cons (by exact certified0154swap)
  apply certified_cons (by exact certified0155)
  apply certified_cons (by exact certified0156)
  apply certified_cons (by exact certified0156swap)
  apply certified_cons (by exact certified0157)
  apply certified_cons (by exact certified0157swap)
  apply certified_cons (by exact certified0158)
  apply certified_cons (by exact certified0159)
  apply certified_cons (by exact certified0160)
  apply certified_cons (by exact certified0160swap)
  apply certified_cons (by exact certified0161)
  apply certified_cons (by exact certified0161swap)
  apply certified_cons (by exact certified0162)
  apply certified_cons (by exact certified0162swap)
  apply certified_cons (by exact certified0163)
  apply certified_cons (by exact certified0163swap)
  apply certified_cons (by exact certified0164)
  apply certified_cons (by exact certified0164swap)
  apply certified_cons (by exact certified0165)
  apply certified_cons (by exact certified0166)
  apply certified_cons (by exact certified0166swap)
  apply certified_cons (by exact certified0167)
  apply certified_cons (by exact certified0167swap)
  apply certified_cons (by exact certified0168)
  apply certified_cons (by exact certified0168swap)
  apply certified_cons (by exact certified0169)
  apply certified_cons (by exact certified0170)
  apply certified_cons (by exact certified0170swap)
  apply certified_cons (by exact certified0171)
  apply certified_cons (by exact certified0172)
  apply certified_cons (by exact certified0172swap)
  apply certified_cons (by exact certified0173)
  apply certified_cons (by exact certified0173swap)
  apply certified_cons (by exact certified0174)
  apply certified_cons (by exact certified0174swap)
  apply certified_cons (by exact certified0175)
  apply certified_cons (by exact certified0175swap)
  apply certified_cons (by exact certified0176)
  apply certified_cons (by exact certified0176swap)
  apply certified_cons (by exact certified0177)
  apply certified_cons (by exact certified0178)
  apply certified_cons (by exact certified0178swap)
  apply certified_cons (by exact certified0179)
  apply certified_cons (by exact certified0179swap)
  apply certified_cons (by exact certified0180)
  apply certified_cons (by exact certified0180swap)
  apply certified_cons (by exact certified0181)
  apply certified_cons (by exact certified0182)
  apply certified_cons (by exact certified0182swap)
  apply certified_cons (by exact certified0183)
  apply certified_cons (by exact certified0184)
  apply certified_cons (by exact certified0184swap)
  apply certified_cons (by exact certified0185)
  apply certified_cons (by exact certified0185swap)
  apply certified_cons (by exact certified0186)
  apply certified_cons (by exact certified0186swap)
  apply certified_cons (by exact certified0187)
  apply certified_cons (by exact certified0187swap)
  apply certified_cons (by exact certified0188)
  apply certified_cons (by exact certified0188swap)
  apply certified_cons (by exact certified0189)
  apply certified_cons (by exact certified0190)
  apply certified_cons (by exact certified0190swap)
  apply certified_cons (by exact certified0191)
  apply certified_cons (by exact certified0191swap)
  apply certified_cons (by exact certified0192)
  apply certified_cons (by exact certified0192swap)
  apply certified_cons (by exact certified0193)
  apply certified_cons (by exact certified0194)
  apply certified_cons (by exact certified0194swap)
  apply certified_cons (by exact certified0195)
  apply certified_cons (by exact certified0196)
  apply certified_cons (by exact certified0196swap)
  apply certified_cons (by exact certified0197)
  apply certified_cons (by exact certified0197swap)
  apply certified_cons (by exact certified0198)
  apply certified_cons (by exact certified0198swap)
  apply certified_cons (by exact certified0199)
  apply certified_cons (by exact certified0199swap)
  simp
#print axioms certified_keys03
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
