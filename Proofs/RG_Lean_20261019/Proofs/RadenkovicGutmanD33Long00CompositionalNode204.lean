/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode194
import Proofs.RadenkovicGutmanD33Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[66],[0]],[[0,0],[0]],[[1056,0],[0]],[[0,0],[0]],[[7062,0],[0]],[[0,0],[0]],[[25608,0],[0]],[[0,0],[0]],[[54648,0],[0]],[[0,0],[0]],[[69696,66],[66]],[[0,0],[0]],[[51414,462],[462]],[[0,0],[0]],[[19800,1056],[1056]],[[0,0],[0]],[[2970,858],[858]],[[0,0],[0]],[[0,198],[198]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
