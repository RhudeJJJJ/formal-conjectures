/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode204
import Proofs.RadenkovicGutmanD33Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[66,0],[0]],[[0,0],[0]],[[1056,0],[0]],[[0,0],[0]],[[7062,0],[0]],[[0,0],[0]],[[25608,0],[0]],[[0,0],[0]],[[54648,0],[0]],[[0,0],[0]],[[69696,66],[66]],[[0,0],[0]],[[51414,462],[462]],[[0,0],[0]],[[19800,1056],[1056]],[[0,0],[0]],[[2970,858],[858]],[[0,0],[0]],[[0,198],[198]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
