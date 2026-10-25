/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode171
import Proofs.RadenkovicGutmanD35Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[70,0],[0]],[[0,0],[0]],[[1050,0],[0]],[[0,0],[0]],[[6580,0],[0]],[[0,0],[0]],[[22330,0],[0]],[[0,0],[0]],[[44520,0],[0]],[[0,0],[0]],[[52990,35],[35]],[[0,0],[0]],[[36540,245],[245]],[[0,0],[0]],[[13230,560],[560]],[[0,0],[0]],[[1890,455],[455]],[[0,0],[0]],[[0,105],[105]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
