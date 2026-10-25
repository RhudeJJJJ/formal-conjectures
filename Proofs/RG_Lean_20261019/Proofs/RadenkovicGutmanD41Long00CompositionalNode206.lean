/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode203
import Proofs.RadenkovicGutmanD41Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[157,0],[0,0]],[[0,0],[0,0]],[[2253,0],[0,0]],[[0,0],[0,0]],[[14738,0],[0,0]],[[0,0],[0,0]],[[53809,0],[0,0]],[[0,0],[0,0]],[[117760,2],[2,0]],[[0,0],[0,0]],[[156856,139],[139,0]],[[0,0],[0,0]],[[123902,946],[946,0]],[[0,0],[0,0]],[[53495,2262],[2262,0]],[[0,0],[0,0]],[[10227,2068],[2068,0]],[[0,0],[0,0]],[[369,615],[615,2]],[[0],[0,0]],[[0],[0,41]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
