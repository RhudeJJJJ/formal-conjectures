/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode036
import Proofs.RadenkovicGutmanD35Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-66]],[[0,0],[0]],[[666,-594],[-594]],[[0,0],[0]],[[426,-1584],[-1584]],[[0,0],[0]],[[-8902,-1452],[-1452]],[[0,0],[0]],[[-30260,-528],[-528]],[[0,0],[0]],[[-46344,-66],[-66]],[[0]],[[-39976]],[[0]],[[-20406]],[[0]],[[-6092]],[[0]],[[-982]],[[0]],[[-66]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
