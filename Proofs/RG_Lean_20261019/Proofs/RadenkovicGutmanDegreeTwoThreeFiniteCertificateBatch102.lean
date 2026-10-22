/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5100
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5101
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5102
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5103
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5104
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5105
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5106
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5107
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5108
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5109
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5110
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5111
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5112
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5113
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5114
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5115
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5116
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5117
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5118
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5119
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5120
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5121
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5122
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5123
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5124
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5125
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5126
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5127
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5128
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5129
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5130
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5131
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5132
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5133
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5134
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5135
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5136
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5137
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5138
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5139
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5140
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5141
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5142
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5143
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5144
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5145
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5146
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5147
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5148
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5149
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
