/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteKeysData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0150
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0151
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0152
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0153
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0154
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0155
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0156
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0157
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0158
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0159
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0160
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0161
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0162
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0163
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0164
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0165
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0166
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0167
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0168
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0169
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0170
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0171
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0172
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0173
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0174
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0175
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0176
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0177
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0178
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0179
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0180
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0181
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0182
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0183
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0184
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0185
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0186
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0187
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0188
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0189
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0190
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0191
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0192
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0193
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0194
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0195
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0196
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0197
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0198
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0199
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneMiddleResidualFiniteActualCases
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
  apply certified_cons (by exact certified0174swap)
  apply certified_cons (by exact certified0175)
  apply certified_cons (by exact certified0175swap)
  apply certified_cons (by exact certified0176)
  apply certified_cons (by exact certified0176swap)
  apply certified_cons (by exact certified0177)
  apply certified_cons (by exact certified0177swap)
  apply certified_cons (by exact certified0178)
  apply certified_cons (by exact certified0178swap)
  apply certified_cons (by exact certified0179)
  apply certified_cons (by exact certified0179swap)
  apply certified_cons (by exact certified0180)
  apply certified_cons (by exact certified0180swap)
  apply certified_cons (by exact certified0181)
  apply certified_cons (by exact certified0181swap)
  apply certified_cons (by exact certified0182)
  apply certified_cons (by exact certified0182swap)
  apply certified_cons (by exact certified0183)
  apply certified_cons (by exact certified0183swap)
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
  apply certified_cons (by exact certified0189swap)
  apply certified_cons (by exact certified0190)
  apply certified_cons (by exact certified0190swap)
  apply certified_cons (by exact certified0191)
  apply certified_cons (by exact certified0191swap)
  apply certified_cons (by exact certified0192)
  apply certified_cons (by exact certified0192swap)
  apply certified_cons (by exact certified0193)
  apply certified_cons (by exact certified0193swap)
  apply certified_cons (by exact certified0194)
  apply certified_cons (by exact certified0195)
  apply certified_cons (by exact certified0196)
  apply certified_cons (by exact certified0197)
  apply certified_cons (by exact certified0198)
  apply certified_cons (by exact certified0199)
  simp
#print axioms certified_keys003
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
