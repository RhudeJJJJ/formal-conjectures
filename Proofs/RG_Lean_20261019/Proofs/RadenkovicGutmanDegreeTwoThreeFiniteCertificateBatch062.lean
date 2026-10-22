/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3100
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3101
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3102
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3103
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3104
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3105
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3106
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3107
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3108
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3109
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3110
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3111
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3112
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3113
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3114
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3115
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3116
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3117
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3118
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3119
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3120
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3121
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3122
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3123
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3124
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3125
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3126
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3127
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3128
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3129
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3130
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3131
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3132
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3133
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3134
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3135
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3136
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3137
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3138
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3139
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3140
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3141
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3142
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3143
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3144
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3145
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3146
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3147
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3148
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase3149
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys062 : ∀ k ∈ keys062, Certified k := by
  apply certified_cons (by exact certified3100)
  apply certified_cons (by exact certified3100swap)
  apply certified_cons (by exact certified3101)
  apply certified_cons (by exact certified3101swap)
  apply certified_cons (by exact certified3102)
  apply certified_cons (by exact certified3102swap)
  apply certified_cons (by exact certified3103)
  apply certified_cons (by exact certified3103swap)
  apply certified_cons (by exact certified3104)
  apply certified_cons (by exact certified3104swap)
  apply certified_cons (by exact certified3105)
  apply certified_cons (by exact certified3105swap)
  apply certified_cons (by exact certified3106)
  apply certified_cons (by exact certified3106swap)
  apply certified_cons (by exact certified3107)
  apply certified_cons (by exact certified3107swap)
  apply certified_cons (by exact certified3108)
  apply certified_cons (by exact certified3108swap)
  apply certified_cons (by exact certified3109)
  apply certified_cons (by exact certified3109swap)
  apply certified_cons (by exact certified3110)
  apply certified_cons (by exact certified3110swap)
  apply certified_cons (by exact certified3111)
  apply certified_cons (by exact certified3111swap)
  apply certified_cons (by exact certified3112)
  apply certified_cons (by exact certified3112swap)
  apply certified_cons (by exact certified3113)
  apply certified_cons (by exact certified3113swap)
  apply certified_cons (by exact certified3114)
  apply certified_cons (by exact certified3114swap)
  apply certified_cons (by exact certified3115)
  apply certified_cons (by exact certified3115swap)
  apply certified_cons (by exact certified3116)
  apply certified_cons (by exact certified3116swap)
  apply certified_cons (by exact certified3117)
  apply certified_cons (by exact certified3117swap)
  apply certified_cons (by exact certified3118)
  apply certified_cons (by exact certified3118swap)
  apply certified_cons (by exact certified3119)
  apply certified_cons (by exact certified3119swap)
  apply certified_cons (by exact certified3120)
  apply certified_cons (by exact certified3120swap)
  apply certified_cons (by exact certified3121)
  apply certified_cons (by exact certified3121swap)
  apply certified_cons (by exact certified3122)
  apply certified_cons (by exact certified3122swap)
  apply certified_cons (by exact certified3123)
  apply certified_cons (by exact certified3123swap)
  apply certified_cons (by exact certified3124)
  apply certified_cons (by exact certified3124swap)
  apply certified_cons (by exact certified3125)
  apply certified_cons (by exact certified3125swap)
  apply certified_cons (by exact certified3126)
  apply certified_cons (by exact certified3126swap)
  apply certified_cons (by exact certified3127)
  apply certified_cons (by exact certified3127swap)
  apply certified_cons (by exact certified3128)
  apply certified_cons (by exact certified3128swap)
  apply certified_cons (by exact certified3129)
  apply certified_cons (by exact certified3129swap)
  apply certified_cons (by exact certified3130)
  apply certified_cons (by exact certified3130swap)
  apply certified_cons (by exact certified3131)
  apply certified_cons (by exact certified3131swap)
  apply certified_cons (by exact certified3132)
  apply certified_cons (by exact certified3132swap)
  apply certified_cons (by exact certified3133)
  apply certified_cons (by exact certified3133swap)
  apply certified_cons (by exact certified3134)
  apply certified_cons (by exact certified3134swap)
  apply certified_cons (by exact certified3135)
  apply certified_cons (by exact certified3135swap)
  apply certified_cons (by exact certified3136)
  apply certified_cons (by exact certified3136swap)
  apply certified_cons (by exact certified3137)
  apply certified_cons (by exact certified3137swap)
  apply certified_cons (by exact certified3138)
  apply certified_cons (by exact certified3138swap)
  apply certified_cons (by exact certified3139)
  apply certified_cons (by exact certified3139swap)
  apply certified_cons (by exact certified3140)
  apply certified_cons (by exact certified3140swap)
  apply certified_cons (by exact certified3141)
  apply certified_cons (by exact certified3141swap)
  apply certified_cons (by exact certified3142)
  apply certified_cons (by exact certified3142swap)
  apply certified_cons (by exact certified3143)
  apply certified_cons (by exact certified3143swap)
  apply certified_cons (by exact certified3144)
  apply certified_cons (by exact certified3144swap)
  apply certified_cons (by exact certified3145)
  apply certified_cons (by exact certified3145swap)
  apply certified_cons (by exact certified3146)
  apply certified_cons (by exact certified3146swap)
  apply certified_cons (by exact certified3147)
  apply certified_cons (by exact certified3147swap)
  apply certified_cons (by exact certified3148)
  apply certified_cons (by exact certified3148swap)
  apply certified_cons (by exact certified3149)
  apply certified_cons (by exact certified3149swap)
  simp
#print axioms certified_keys062
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
