/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode165
import Proofs.RadenkovicGutmanD19Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-34],[0]],[[0,0],[0]],[[-464,0],[0,0]],[[0,0],[0,0]],[[-2514,0],[0,0]],[[0,0],[0,0]],[[-6626,0],[0,0]],[[0,0],[0,0]],[[-7502,0],[0,0]],[[0,0],[0,0]],[[2016,-34],[-34,0]],[[0,0],[0,0]],[[14954,-253],[-253,0]],[[0,0],[0,0]],[[16278,-615],[-615,0]],[[0,0],[0,0]],[[7704,-512],[-512,0]],[[0,0],[0,0]],[[1404,-59],[-59,0]],[[0,0],[0,0]],[[0,57],[57,-34]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
