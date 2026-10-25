/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode036
import Proofs.RadenkovicGutmanD42Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-80]],[[0,0],[0]],[[792,-720],[-720]],[[0,0],[0]],[[384,-1920],[-1920]],[[0,0],[0]],[[-11240,-1760],[-1760]],[[0,0],[0]],[[-37456,-640],[-640]],[[0,0],[0]],[[-56928,-80],[-80]],[[0]],[[-48880]],[[0]],[[-24872]],[[0]],[[-7408]],[[0]],[[-1192]],[[0]],[[-80]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
