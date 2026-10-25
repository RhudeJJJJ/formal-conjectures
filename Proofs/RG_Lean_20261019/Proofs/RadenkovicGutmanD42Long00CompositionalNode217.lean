/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode034
import Proofs.RadenkovicGutmanD42Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-84],[0]],[[0,0],[0]],[[-1260,0],[0]],[[0,0],[0]],[[-7896,0],[0]],[[0,0],[0]],[[-26796,0],[0]],[[0,0],[0]],[[-53424,0],[0]],[[0,0],[0]],[[-63588,-42],[-42]],[[0,0],[0]],[[-43848,-294],[-294]],[[0,0],[0]],[[-15876,-672],[-672]],[[0,0],[0]],[[-2268,-546],[-546]],[[0,0],[0]],[[0,-126],[-126]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
