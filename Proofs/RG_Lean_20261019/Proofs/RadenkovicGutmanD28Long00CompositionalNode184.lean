/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode030
import Proofs.RadenkovicGutmanD28Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[28],[0]],[[0,0],[0]],[[448,0],[0]],[[0,0],[0]],[[2996,0],[0]],[[0,0],[0]],[[10864,0],[0]],[[0,0],[0]],[[23184,0],[0]],[[0,0],[0]],[[29568,28],[28]],[[0,0],[0]],[[21812,196],[196]],[[0,0],[0]],[[8400,448],[448]],[[0,0],[0]],[[1260,364],[364]],[[0,0],[0]],[[0,84],[84]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
