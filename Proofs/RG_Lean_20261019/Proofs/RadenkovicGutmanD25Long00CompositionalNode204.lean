/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode194
import Proofs.RadenkovicGutmanD25Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[50],[0]],[[0,0],[0]],[[800,0],[0]],[[0,0],[0]],[[5350,0],[0]],[[0,0],[0]],[[19400,0],[0]],[[0,0],[0]],[[41400,0],[0]],[[0,0],[0]],[[52800,50],[50]],[[0,0],[0]],[[38950,350],[350]],[[0,0],[0]],[[15000,800],[800]],[[0,0],[0]],[[2250,650],[650]],[[0,0],[0]],[[0,150],[150]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
