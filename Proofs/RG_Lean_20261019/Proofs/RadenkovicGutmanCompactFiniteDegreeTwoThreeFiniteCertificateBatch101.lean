/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5050
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5051
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5052
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5053
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5054
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5055
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5056
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5057
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5058
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5059
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5060
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5061
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5062
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5063
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5064
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5065
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5066
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5067
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5068
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5069
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5070
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5071
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5072
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5073
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5074
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5075
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5076
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5077
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5078
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5079
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5080
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5081
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5082
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5083
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5084
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5085
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5086
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5087
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5088
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5089
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5090
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5091
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5092
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5093
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5094
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5095
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5096
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5097
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5098
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteActualCase5099
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
