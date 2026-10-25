/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode198
import Proofs.RadenkovicGutmanD41Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[239,0],[0,0]],[[0,0],[0,0]],[[3319,0],[0,0]],[[0,0],[0,0]],[[20232,0],[0,0]],[[0,0],[0,0]],[[67667,0],[0,0]],[[0,0],[0,0]],[[133668,2],[2,0]],[[0,0],[0,0]],[[158004,139],[139,0]],[[0,0],[0,0]],[[108076,946],[946,0]],[[0,0],[0,0]],[[38161,2262],[2262,0]],[[0,0],[0,0]],[[4569,2068],[2068,0]],[[0,0],[0,0]],[[-369,615],[615,2]],[[0],[0,0]],[[0],[0,41]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
