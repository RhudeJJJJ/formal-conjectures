/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode165
import Proofs.RadenkovicGutmanD6Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-8],[0]],[[0,0],[0]],[[-100,0],[0,0]],[[0,0],[0,0]],[[-460,0],[0,0]],[[0,0],[0,0]],[[-776,0],[0,0]],[[0,0],[0,0]],[[740,0],[0,0]],[[0,0],[0,0]],[[5136,-8],[-8,0]],[[0,0],[0,0]],[[8636,-58],[-58,0]],[[0,0],[0,0]],[[7048,-134],[-134,0]],[[0,0],[0,0]],[[2868,-96],[-96,0]],[[0,0],[0,0]],[[468,6],[6,0]],[[0,0],[0,0]],[[0,18],[18,-8]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
