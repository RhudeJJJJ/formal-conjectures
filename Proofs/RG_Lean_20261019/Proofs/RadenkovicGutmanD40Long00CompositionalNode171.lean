/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode030
import Proofs.RadenkovicGutmanD40Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[80],[0]],[[0,0],[0]],[[1200,0],[0]],[[0,0],[0]],[[7520,0],[0]],[[0,0],[0]],[[25520,0],[0]],[[0,0],[0]],[[50880,0],[0]],[[0,0],[0]],[[60560,40],[40]],[[0,0],[0]],[[41760,280],[280]],[[0,0],[0]],[[15120,640],[640]],[[0,0],[0]],[[2160,520],[520]],[[0,0],[0]],[[0,120],[120]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
