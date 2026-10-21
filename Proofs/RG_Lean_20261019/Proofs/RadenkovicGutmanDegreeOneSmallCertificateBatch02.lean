/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0100
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0101
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0102
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0103
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0104
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0105
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0106
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0107
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0108
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0109
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0110
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0111
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0112
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0113
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0114
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0115
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0116
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0117
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0118
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0119
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0120
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0121
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0122
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0123
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0124
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0125
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0126
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0127
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0128
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0129
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0130
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0131
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0132
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0133
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0134
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0135
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0136
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0137
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0138
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0139
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0140
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0141
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0142
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0143
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0144
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0145
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0146
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0147
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0148
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0149
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys02 : ∀ k ∈ keys02, Certified k := by
  apply certified_cons (by exact certified0100)
  apply certified_cons (by exact certified0100swap)
  apply certified_cons (by exact certified0101)
  apply certified_cons (by exact certified0101swap)
  apply certified_cons (by exact certified0102)
  apply certified_cons (by exact certified0103)
  apply certified_cons (by exact certified0103swap)
  apply certified_cons (by exact certified0104)
  apply certified_cons (by exact certified0104swap)
  apply certified_cons (by exact certified0105)
  apply certified_cons (by exact certified0105swap)
  apply certified_cons (by exact certified0106)
  apply certified_cons (by exact certified0106swap)
  apply certified_cons (by exact certified0107)
  apply certified_cons (by exact certified0108)
  apply certified_cons (by exact certified0108swap)
  apply certified_cons (by exact certified0109)
  apply certified_cons (by exact certified0109swap)
  apply certified_cons (by exact certified0110)
  apply certified_cons (by exact certified0111)
  apply certified_cons (by exact certified0112)
  apply certified_cons (by exact certified0112swap)
  apply certified_cons (by exact certified0113)
  apply certified_cons (by exact certified0113swap)
  apply certified_cons (by exact certified0114)
  apply certified_cons (by exact certified0114swap)
  apply certified_cons (by exact certified0115)
  apply certified_cons (by exact certified0115swap)
  apply certified_cons (by exact certified0116)
  apply certified_cons (by exact certified0116swap)
  apply certified_cons (by exact certified0117)
  apply certified_cons (by exact certified0117swap)
  apply certified_cons (by exact certified0118)
  apply certified_cons (by exact certified0119)
  apply certified_cons (by exact certified0119swap)
  apply certified_cons (by exact certified0120)
  apply certified_cons (by exact certified0120swap)
  apply certified_cons (by exact certified0121)
  apply certified_cons (by exact certified0121swap)
  apply certified_cons (by exact certified0122)
  apply certified_cons (by exact certified0122swap)
  apply certified_cons (by exact certified0123)
  apply certified_cons (by exact certified0124)
  apply certified_cons (by exact certified0124swap)
  apply certified_cons (by exact certified0125)
  apply certified_cons (by exact certified0125swap)
  apply certified_cons (by exact certified0126)
  apply certified_cons (by exact certified0127)
  apply certified_cons (by exact certified0128)
  apply certified_cons (by exact certified0128swap)
  apply certified_cons (by exact certified0129)
  apply certified_cons (by exact certified0129swap)
  apply certified_cons (by exact certified0130)
  apply certified_cons (by exact certified0130swap)
  apply certified_cons (by exact certified0131)
  apply certified_cons (by exact certified0131swap)
  apply certified_cons (by exact certified0132)
  apply certified_cons (by exact certified0132swap)
  apply certified_cons (by exact certified0133)
  apply certified_cons (by exact certified0133swap)
  apply certified_cons (by exact certified0134)
  apply certified_cons (by exact certified0135)
  apply certified_cons (by exact certified0135swap)
  apply certified_cons (by exact certified0136)
  apply certified_cons (by exact certified0136swap)
  apply certified_cons (by exact certified0137)
  apply certified_cons (by exact certified0137swap)
  apply certified_cons (by exact certified0138)
  apply certified_cons (by exact certified0138swap)
  apply certified_cons (by exact certified0139)
  apply certified_cons (by exact certified0140)
  apply certified_cons (by exact certified0140swap)
  apply certified_cons (by exact certified0141)
  apply certified_cons (by exact certified0141swap)
  apply certified_cons (by exact certified0142)
  apply certified_cons (by exact certified0143)
  apply certified_cons (by exact certified0144)
  apply certified_cons (by exact certified0144swap)
  apply certified_cons (by exact certified0145)
  apply certified_cons (by exact certified0145swap)
  apply certified_cons (by exact certified0146)
  apply certified_cons (by exact certified0146swap)
  apply certified_cons (by exact certified0147)
  apply certified_cons (by exact certified0147swap)
  apply certified_cons (by exact certified0148)
  apply certified_cons (by exact certified0148swap)
  apply certified_cons (by exact certified0149)
  apply certified_cons (by exact certified0149swap)
  simp
#print axioms certified_keys02
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
