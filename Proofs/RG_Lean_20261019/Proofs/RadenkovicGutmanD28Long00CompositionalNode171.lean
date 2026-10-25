/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode030
import Proofs.RadenkovicGutmanD28Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[56],[0]],[[0,0],[0]],[[840,0],[0]],[[0,0],[0]],[[5264,0],[0]],[[0,0],[0]],[[17864,0],[0]],[[0,0],[0]],[[35616,0],[0]],[[0,0],[0]],[[42392,28],[28]],[[0,0],[0]],[[29232,196],[196]],[[0,0],[0]],[[10584,448],[448]],[[0,0],[0]],[[1512,364],[364]],[[0,0],[0]],[[0,84],[84]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
