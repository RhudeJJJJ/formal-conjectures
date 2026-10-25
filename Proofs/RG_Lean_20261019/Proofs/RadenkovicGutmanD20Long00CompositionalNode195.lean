/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode194
import Proofs.RadenkovicGutmanD20Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[80],[0]],[[0,0],[0]],[[1200,0],[0]],[[0,0],[0]],[[7520,0],[0]],[[0,0],[0]],[[25520,0],[0]],[[0,0],[0]],[[50880,0],[0]],[[0,0],[0]],[[60560,40],[40]],[[0,0],[0]],[[41760,280],[280]],[[0,0],[0]],[[15120,640],[640]],[[0,0],[0]],[[2160,520],[520]],[[0,0],[0]],[[0,120],[120]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
