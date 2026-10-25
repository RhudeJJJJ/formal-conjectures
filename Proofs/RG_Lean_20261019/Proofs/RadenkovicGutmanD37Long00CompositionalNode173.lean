/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode165
import Proofs.RadenkovicGutmanD37Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-70],[0]],[[0,0],[0]],[[-968,0],[0,0]],[[0,0],[0,0]],[[-5358,0],[0,0]],[[0,0],[0,0]],[[-14726,0],[0,0]],[[0,0],[0,0]],[[-18914,0],[0,0]],[[0,0],[0,0]],[[-2304,-70],[-70,0]],[[0,0],[0,0]],[[23702,-523],[-523,0]],[[0,0],[0,0]],[[29058,-1281],[-1281,0]],[[0,0],[0,0]],[[14400,-1088],[-1088,0]],[[0,0],[0,0]],[[2700,-149],[-149,0]],[[0,0],[0,0]],[[0,111],[111,-70]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
