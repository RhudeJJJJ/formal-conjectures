/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5100
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5101
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5102
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5103
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5104
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5105
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5106
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5107
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5108
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5109
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5110
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5111
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5112
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5113
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5114
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5115
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5116
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5117
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5118
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5119
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5120
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5121
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5122
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5123
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5124
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5125
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5126
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5127
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5128
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5129
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5130
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5131
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5132
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5133
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5134
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5135
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5136
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5137
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5138
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5139
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5140
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5141
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5142
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5143
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5144
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5145
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5146
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5147
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5148
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5149
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys102 : ∀ k ∈ keys102, Certified k := by
  apply certified_cons (by exact certified5100)
  apply certified_cons (by exact certified5100swap)
  apply certified_cons (by exact certified5101)
  apply certified_cons (by exact certified5101swap)
  apply certified_cons (by exact certified5102)
  apply certified_cons (by exact certified5102swap)
  apply certified_cons (by exact certified5103)
  apply certified_cons (by exact certified5103swap)
  apply certified_cons (by exact certified5104)
  apply certified_cons (by exact certified5104swap)
  apply certified_cons (by exact certified5105)
  apply certified_cons (by exact certified5105swap)
  apply certified_cons (by exact certified5106)
  apply certified_cons (by exact certified5106swap)
  apply certified_cons (by exact certified5107)
  apply certified_cons (by exact certified5107swap)
  apply certified_cons (by exact certified5108)
  apply certified_cons (by exact certified5108swap)
  apply certified_cons (by exact certified5109)
  apply certified_cons (by exact certified5109swap)
  apply certified_cons (by exact certified5110)
  apply certified_cons (by exact certified5110swap)
  apply certified_cons (by exact certified5111)
  apply certified_cons (by exact certified5111swap)
  apply certified_cons (by exact certified5112)
  apply certified_cons (by exact certified5112swap)
  apply certified_cons (by exact certified5113)
  apply certified_cons (by exact certified5113swap)
  apply certified_cons (by exact certified5114)
  apply certified_cons (by exact certified5114swap)
  apply certified_cons (by exact certified5115)
  apply certified_cons (by exact certified5115swap)
  apply certified_cons (by exact certified5116)
  apply certified_cons (by exact certified5116swap)
  apply certified_cons (by exact certified5117)
  apply certified_cons (by exact certified5117swap)
  apply certified_cons (by exact certified5118)
  apply certified_cons (by exact certified5118swap)
  apply certified_cons (by exact certified5119)
  apply certified_cons (by exact certified5119swap)
  apply certified_cons (by exact certified5120)
  apply certified_cons (by exact certified5120swap)
  apply certified_cons (by exact certified5121)
  apply certified_cons (by exact certified5121swap)
  apply certified_cons (by exact certified5122)
  apply certified_cons (by exact certified5122swap)
  apply certified_cons (by exact certified5123)
  apply certified_cons (by exact certified5123swap)
  apply certified_cons (by exact certified5124)
  apply certified_cons (by exact certified5124swap)
  apply certified_cons (by exact certified5125)
  apply certified_cons (by exact certified5125swap)
  apply certified_cons (by exact certified5126)
  apply certified_cons (by exact certified5126swap)
  apply certified_cons (by exact certified5127)
  apply certified_cons (by exact certified5127swap)
  apply certified_cons (by exact certified5128)
  apply certified_cons (by exact certified5128swap)
  apply certified_cons (by exact certified5129)
  apply certified_cons (by exact certified5129swap)
  apply certified_cons (by exact certified5130)
  apply certified_cons (by exact certified5130swap)
  apply certified_cons (by exact certified5131)
  apply certified_cons (by exact certified5131swap)
  apply certified_cons (by exact certified5132)
  apply certified_cons (by exact certified5132swap)
  apply certified_cons (by exact certified5133)
  apply certified_cons (by exact certified5133swap)
  apply certified_cons (by exact certified5134)
  apply certified_cons (by exact certified5134swap)
  apply certified_cons (by exact certified5135)
  apply certified_cons (by exact certified5135swap)
  apply certified_cons (by exact certified5136)
  apply certified_cons (by exact certified5136swap)
  apply certified_cons (by exact certified5137)
  apply certified_cons (by exact certified5137swap)
  apply certified_cons (by exact certified5138)
  apply certified_cons (by exact certified5138swap)
  apply certified_cons (by exact certified5139)
  apply certified_cons (by exact certified5139swap)
  apply certified_cons (by exact certified5140)
  apply certified_cons (by exact certified5140swap)
  apply certified_cons (by exact certified5141)
  apply certified_cons (by exact certified5141swap)
  apply certified_cons (by exact certified5142)
  apply certified_cons (by exact certified5142swap)
  apply certified_cons (by exact certified5143)
  apply certified_cons (by exact certified5143swap)
  apply certified_cons (by exact certified5144)
  apply certified_cons (by exact certified5144swap)
  apply certified_cons (by exact certified5145)
  apply certified_cons (by exact certified5145swap)
  apply certified_cons (by exact certified5146)
  apply certified_cons (by exact certified5146swap)
  apply certified_cons (by exact certified5147)
  apply certified_cons (by exact certified5147swap)
  apply certified_cons (by exact certified5148)
  apply certified_cons (by exact certified5148swap)
  apply certified_cons (by exact certified5149)
  apply certified_cons (by exact certified5149swap)
  simp
#print axioms certified_keys102
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
