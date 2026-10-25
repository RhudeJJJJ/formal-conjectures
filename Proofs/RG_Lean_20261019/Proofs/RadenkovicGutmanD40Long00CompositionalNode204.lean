/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode194
import Proofs.RadenkovicGutmanD40Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[80],[0]],[[0,0],[0]],[[1280,0],[0]],[[0,0],[0]],[[8560,0],[0]],[[0,0],[0]],[[31040,0],[0]],[[0,0],[0]],[[66240,0],[0]],[[0,0],[0]],[[84480,80],[80]],[[0,0],[0]],[[62320,560],[560]],[[0,0],[0]],[[24000,1280],[1280]],[[0,0],[0]],[[3600,1040],[1040]],[[0,0],[0]],[[0,240],[240]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
