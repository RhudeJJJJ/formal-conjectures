/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5050
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5051
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5052
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5053
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5054
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5055
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5056
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5057
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5058
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5059
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5060
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5061
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5062
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5063
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5064
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5065
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5066
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5067
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5068
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5069
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5070
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5071
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5072
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5073
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5074
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5075
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5076
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5077
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5078
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5079
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5080
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5081
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5082
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5083
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5084
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5085
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5086
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5087
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5088
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5089
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5090
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5091
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5092
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5093
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5094
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5095
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5096
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5097
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5098
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5099
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys101 : ∀ k ∈ keys101, Certified k := by
  apply certified_cons (by exact certified5050)
  apply certified_cons (by exact certified5051)
  apply certified_cons (by exact certified5052)
  apply certified_cons (by exact certified5053)
  apply certified_cons (by exact certified5054)
  apply certified_cons (by exact certified5054swap)
  apply certified_cons (by exact certified5055)
  apply certified_cons (by exact certified5055swap)
  apply certified_cons (by exact certified5056)
  apply certified_cons (by exact certified5056swap)
  apply certified_cons (by exact certified5057)
  apply certified_cons (by exact certified5057swap)
  apply certified_cons (by exact certified5058)
  apply certified_cons (by exact certified5058swap)
  apply certified_cons (by exact certified5059)
  apply certified_cons (by exact certified5059swap)
  apply certified_cons (by exact certified5060)
  apply certified_cons (by exact certified5060swap)
  apply certified_cons (by exact certified5061)
  apply certified_cons (by exact certified5061swap)
  apply certified_cons (by exact certified5062)
  apply certified_cons (by exact certified5062swap)
  apply certified_cons (by exact certified5063)
  apply certified_cons (by exact certified5063swap)
  apply certified_cons (by exact certified5064)
  apply certified_cons (by exact certified5064swap)
  apply certified_cons (by exact certified5065)
  apply certified_cons (by exact certified5065swap)
  apply certified_cons (by exact certified5066)
  apply certified_cons (by exact certified5066swap)
  apply certified_cons (by exact certified5067)
  apply certified_cons (by exact certified5067swap)
  apply certified_cons (by exact certified5068)
  apply certified_cons (by exact certified5068swap)
  apply certified_cons (by exact certified5069)
  apply certified_cons (by exact certified5069swap)
  apply certified_cons (by exact certified5070)
  apply certified_cons (by exact certified5070swap)
  apply certified_cons (by exact certified5071)
  apply certified_cons (by exact certified5071swap)
  apply certified_cons (by exact certified5072)
  apply certified_cons (by exact certified5072swap)
  apply certified_cons (by exact certified5073)
  apply certified_cons (by exact certified5073swap)
  apply certified_cons (by exact certified5074)
  apply certified_cons (by exact certified5074swap)
  apply certified_cons (by exact certified5075)
  apply certified_cons (by exact certified5075swap)
  apply certified_cons (by exact certified5076)
  apply certified_cons (by exact certified5076swap)
  apply certified_cons (by exact certified5077)
  apply certified_cons (by exact certified5077swap)
  apply certified_cons (by exact certified5078)
  apply certified_cons (by exact certified5078swap)
  apply certified_cons (by exact certified5079)
  apply certified_cons (by exact certified5079swap)
  apply certified_cons (by exact certified5080)
  apply certified_cons (by exact certified5080swap)
  apply certified_cons (by exact certified5081)
  apply certified_cons (by exact certified5081swap)
  apply certified_cons (by exact certified5082)
  apply certified_cons (by exact certified5082swap)
  apply certified_cons (by exact certified5083)
  apply certified_cons (by exact certified5083swap)
  apply certified_cons (by exact certified5084)
  apply certified_cons (by exact certified5084swap)
  apply certified_cons (by exact certified5085)
  apply certified_cons (by exact certified5085swap)
  apply certified_cons (by exact certified5086)
  apply certified_cons (by exact certified5086swap)
  apply certified_cons (by exact certified5087)
  apply certified_cons (by exact certified5087swap)
  apply certified_cons (by exact certified5088)
  apply certified_cons (by exact certified5088swap)
  apply certified_cons (by exact certified5089)
  apply certified_cons (by exact certified5089swap)
  apply certified_cons (by exact certified5090)
  apply certified_cons (by exact certified5090swap)
  apply certified_cons (by exact certified5091)
  apply certified_cons (by exact certified5091swap)
  apply certified_cons (by exact certified5092)
  apply certified_cons (by exact certified5092swap)
  apply certified_cons (by exact certified5093)
  apply certified_cons (by exact certified5093swap)
  apply certified_cons (by exact certified5094)
  apply certified_cons (by exact certified5094swap)
  apply certified_cons (by exact certified5095)
  apply certified_cons (by exact certified5095swap)
  apply certified_cons (by exact certified5096)
  apply certified_cons (by exact certified5096swap)
  apply certified_cons (by exact certified5097)
  apply certified_cons (by exact certified5097swap)
  apply certified_cons (by exact certified5098)
  apply certified_cons (by exact certified5098swap)
  apply certified_cons (by exact certified5099)
  apply certified_cons (by exact certified5099swap)
  simp
#print axioms certified_keys101
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
