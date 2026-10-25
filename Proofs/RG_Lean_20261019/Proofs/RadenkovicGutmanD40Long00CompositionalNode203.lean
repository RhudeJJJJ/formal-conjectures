/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode202
import Proofs.RadenkovicGutmanD40Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[74,0],[0,0]],[[0,0],[0,0]],[[924,0],[0,0]],[[0,0],[0,0]],[[5842,0],[0,0]],[[0,0],[0,0]],[[21512,0],[0,0]],[[0,0],[0,0]],[[48728,2],[2,0]],[[0,0],[0,0]],[[68620,56],[56,0]],[[0,0],[0,0]],[[58594,364],[364,0]],[[0,0],[0,0]],[[28198,928],[928,0]],[[0,0],[0,0]],[[6378,978],[978,0]],[[0,0],[0,0]],[[360,360],[360,2]],[[0],[0,0]],[[0],[0,40]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
