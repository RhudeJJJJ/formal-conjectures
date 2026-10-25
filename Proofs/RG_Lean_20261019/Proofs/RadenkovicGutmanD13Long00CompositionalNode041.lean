/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode036
import Proofs.RadenkovicGutmanD13Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-22]],[[0,0],[0]],[[270,-198],[-198]],[[0,0],[0]],[[558,-528],[-528]],[[0,0],[0]],[[-1554,-484],[-484]],[[0,0],[0]],[[-7644,-176],[-176]],[[0,0],[0]],[[-13080,-22],[-22]],[[0]],[[-11992]],[[0]],[[-6370]],[[0]],[[-1956]],[[0]],[[-322]],[[0]],[[-22]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
