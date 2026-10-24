/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e108 : NestedArithmetic.Expr 3 := .pow e042 2
noncomputable def p108 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,81],[0,162,-36],[81,-36,4]],[[0,0,0],[0,0,0],[0,0]],[[0,4536,378],[4536,-252,-84],[378,-84]],[[0,0,0],[0,0,0],[0,0]],[[63504,42120,441],[42120,-6126,0],[441,0]],[[0,0,0],[0,0,0],[0,0]],[[883008,162108,-414],[162108,-20500,92],[-414,92]],[[0,0,0],[0,0,0],[0,0]],[[5548176,324168,-1200],[324168,-31112,52],[-1200,52]],[[0,0,0],[0,0,0],[0,0]],[[20850384,319740,-582],[319740,-24588,8],[-582,8]],[[0,0,0],[0,0],[0]],[[52289860,20720,445],[20720,-9678],[445]],[[0,0,0],[0,0],[0]],[[92453800,-343768,598],[-343768,-1100],[598]],[[0,0,0],[0,0],[0]],[[118670164,-451316,261],[-451316,466],[261]],[[0,0,0],[0,0],[0]],[[112073800,-302200,52],[-302200,168],[52]],[[0,0,0],[0,0],[0]],[[77908144,-119228,4],[-119228,16],[4]],[[0,0],[0]],[[39264080,-26220],[-26220]],[[0,0],[0]],[[13739452,-1924],[-1924]],[[0,0],[0]],[[2947616,452],[452]],[[0,0],[0]],[[187348,116],[116]],[[0,0],[0]],[[-91896,8],[8]],[[0]],[[-28740]],[[0]],[[-2744]],[[0]],[[200]],[[0]],[[64]],[[0]],[[4]]]
theorem step108 : p108=NestedArithmetic.power p042 2 := by decide +kernel
#print axioms step108
theorem h108 : NestedArithmetic.compile e108=p108 := StagedExprCompile.compile_pow 2 e108 e042 p042 p108 rfl h042 step108
#print axioms h108
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
