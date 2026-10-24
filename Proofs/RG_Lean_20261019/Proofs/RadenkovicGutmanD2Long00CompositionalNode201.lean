/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode191
import Proofs.RadenkovicGutmanD2Long00CompositionalNode181
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .times e191 e181
noncomputable def p201 : NestedHorner.Poly 3 := [[[4],[0]],[[0,0],[0]],[[64,0],[0]],[[0,0],[0]],[[428,0],[0]],[[0,0],[0]],[[1552,0],[0]],[[0,0],[0]],[[3312,0],[0]],[[0,0],[0]],[[4224,4],[4]],[[0,0],[0]],[[3116,28],[28]],[[0,0],[0]],[[1200,64],[64]],[[0,0],[0]],[[180,52],[52]],[[0,0],[0]],[[0,12],[12]]]
theorem step201 : p201=NestedArithmetic.mul p191 p181 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_times e201 e191 e181 p191 p181 p201 rfl h191 h181 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
