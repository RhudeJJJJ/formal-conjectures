/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode030
import Proofs.RadenkovicGutmanD40Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[40],[0]],[[0,0],[0]],[[640,0],[0]],[[0,0],[0]],[[4280,0],[0]],[[0,0],[0]],[[15520,0],[0]],[[0,0],[0]],[[33120,0],[0]],[[0,0],[0]],[[42240,40],[40]],[[0,0],[0]],[[31160,280],[280]],[[0,0],[0]],[[12000,640],[640]],[[0,0],[0]],[[1800,520],[520]],[[0,0],[0]],[[0,120],[120]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
