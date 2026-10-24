/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode201
import Proofs.RadenkovicGutmanD2Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e201 e003
noncomputable def p202 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[4,0],[0]],[[0,0],[0]],[[64,0],[0]],[[0,0],[0]],[[428,0],[0]],[[0,0],[0]],[[1552,0],[0]],[[0,0],[0]],[[3312,0],[0]],[[0,0],[0]],[[4224,4],[4]],[[0,0],[0]],[[3116,28],[28]],[[0,0],[0]],[[1200,64],[64]],[[0,0],[0]],[[180,52],[52]],[[0,0],[0]],[[0,12],[12]]]
theorem step202 : p202=NestedArithmetic.mul p201 p003 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e201 e003 p201 p003 p202 rfl h201 h003 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
