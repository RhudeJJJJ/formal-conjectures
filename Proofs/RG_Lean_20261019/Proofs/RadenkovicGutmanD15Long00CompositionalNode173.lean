/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode165
import Proofs.RadenkovicGutmanD15Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-26],[0]],[[0,0],[0]],[[-352,0],[0,0]],[[0,0],[0,0]],[[-1882,0],[0,0]],[[0,0],[0,0]],[[-4826,0],[0,0]],[[0,0],[0,0]],[[-4966,0],[0,0]],[[0,0],[0,0]],[[2976,-26],[-26,0]],[[0,0],[0,0]],[[13010,-193],[-193,0]],[[0,0],[0,0]],[[13438,-467],[-467,0]],[[0,0],[0,0]],[[6216,-384],[-384,0]],[[0,0],[0,0]],[[1116,-39],[-39,0]],[[0,0],[0,0]],[[0,45],[45,-26]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
