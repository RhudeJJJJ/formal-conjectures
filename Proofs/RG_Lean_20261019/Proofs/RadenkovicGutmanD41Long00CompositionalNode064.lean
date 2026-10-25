/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode062
import Proofs.RadenkovicGutmanD41Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,41]],[[0,0],[0,0]],[[369,615],[615,2]],[[0,0],[0]],[[10227,2068],[2068]],[[0,0],[0]],[[53495,2262],[2262]],[[0,0],[0]],[[123902,946],[946]],[[0,0],[0]],[[156856,139],[139]],[[0,0],[0]],[[117760,2],[2]],[[0]],[[53809]],[[0]],[[14738]],[[0]],[[2253]],[[0]],[[157]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
