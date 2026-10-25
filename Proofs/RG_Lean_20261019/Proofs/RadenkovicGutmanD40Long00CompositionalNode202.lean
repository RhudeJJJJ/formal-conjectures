/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode191
import Proofs.RadenkovicGutmanD40Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[74,0],[0,0]],[[0,0],[0,0]],[[924,0],[0,0]],[[0,0],[0,0]],[[5842,0],[0,0]],[[0,0],[0,0]],[[21512,0],[0,0]],[[0,0],[0,0]],[[48728,2],[2,0]],[[0,0],[0,0]],[[68620,56],[56,0]],[[0,0],[0,0]],[[58594,364],[364,0]],[[0,0],[0,0]],[[28198,928],[928,0]],[[0,0],[0,0]],[[6378,978],[978,0]],[[0,0],[0,0]],[[360,360],[360,2]],[[0],[0,0]],[[0],[0,40]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
