/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode036
import Proofs.RadenkovicGutmanD21Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-38]],[[0,0],[0]],[[414,-342],[-342]],[[0,0],[0]],[[510,-912],[-912]],[[0,0],[0]],[[-4226,-836],[-836]],[[0,0],[0]],[[-15868,-304],[-304]],[[0,0],[0]],[[-25176,-38],[-38]],[[0]],[[-22168]],[[0]],[[-11474]],[[0]],[[-3460]],[[0]],[[-562]],[[0]],[[-38]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
