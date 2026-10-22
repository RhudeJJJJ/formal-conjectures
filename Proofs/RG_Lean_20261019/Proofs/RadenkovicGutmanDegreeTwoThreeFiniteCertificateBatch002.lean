/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0100
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0101
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0102
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0103
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0104
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0105
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0106
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0107
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0108
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0109
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0110
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0111
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0112
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0113
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0114
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0115
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0116
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0117
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0118
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0119
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0120
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0121
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0122
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0123
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0124
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0125
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0126
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0127
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0128
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0129
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0130
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0131
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0132
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0133
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0134
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0135
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0136
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0137
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0138
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0139
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0140
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0141
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0142
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0143
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0144
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0145
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0146
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0147
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0148
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0149
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys002 : ∀ k ∈ keys002, Certified k := by
  apply certified_cons (by exact certified0100)
  apply certified_cons (by exact certified0101)
  apply certified_cons (by exact certified0102)
  apply certified_cons (by exact certified0103)
  apply certified_cons (by exact certified0104)
  apply certified_cons (by exact certified0105)
  apply certified_cons (by exact certified0106)
  apply certified_cons (by exact certified0107)
  apply certified_cons (by exact certified0108)
  apply certified_cons (by exact certified0109)
  apply certified_cons (by exact certified0110)
  apply certified_cons (by exact certified0111)
  apply certified_cons (by exact certified0112)
  apply certified_cons (by exact certified0113)
  apply certified_cons (by exact certified0114)
  apply certified_cons (by exact certified0115)
  apply certified_cons (by exact certified0116)
  apply certified_cons (by exact certified0117)
  apply certified_cons (by exact certified0118)
  apply certified_cons (by exact certified0119)
  apply certified_cons (by exact certified0120)
  apply certified_cons (by exact certified0121)
  apply certified_cons (by exact certified0122)
  apply certified_cons (by exact certified0123)
  apply certified_cons (by exact certified0124)
  apply certified_cons (by exact certified0125)
  apply certified_cons (by exact certified0126)
  apply certified_cons (by exact certified0127)
  apply certified_cons (by exact certified0128)
  apply certified_cons (by exact certified0129)
  apply certified_cons (by exact certified0130)
  apply certified_cons (by exact certified0131)
  apply certified_cons (by exact certified0132)
  apply certified_cons (by exact certified0133)
  apply certified_cons (by exact certified0134)
  apply certified_cons (by exact certified0135)
  apply certified_cons (by exact certified0136)
  apply certified_cons (by exact certified0137)
  apply certified_cons (by exact certified0138)
  apply certified_cons (by exact certified0139)
  apply certified_cons (by exact certified0140)
  apply certified_cons (by exact certified0141)
  apply certified_cons (by exact certified0142)
  apply certified_cons (by exact certified0143)
  apply certified_cons (by exact certified0144)
  apply certified_cons (by exact certified0145)
  apply certified_cons (by exact certified0146)
  apply certified_cons (by exact certified0147)
  apply certified_cons (by exact certified0148)
  apply certified_cons (by exact certified0149)
  simp
#print axioms certified_keys002
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
