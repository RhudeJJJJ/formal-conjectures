/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode165
import Proofs.RadenkovicGutmanD27Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-50],[0]],[[0,0],[0]],[[-688,0],[0,0]],[[0,0],[0,0]],[[-3778,0],[0,0]],[[0,0],[0,0]],[[-10226,0],[0,0]],[[0,0],[0,0]],[[-12574,0],[0,0]],[[0,0],[0,0]],[[96,-50],[-50,0]],[[0,0],[0,0]],[[18842,-373],[-373,0]],[[0,0],[0,0]],[[21958,-911],[-911,0]],[[0,0],[0,0]],[[10680,-768],[-768,0]],[[0,0],[0,0]],[[1980,-99],[-99,0]],[[0,0],[0,0]],[[0,81],[81,-50]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
