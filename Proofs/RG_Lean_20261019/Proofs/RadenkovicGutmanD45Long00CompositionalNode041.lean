/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode036
import Proofs.RadenkovicGutmanD45Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-86]],[[0,0],[0]],[[846,-774],[-774]],[[0,0],[0]],[[366,-2064],[-2064]],[[0,0],[0]],[[-12242,-1892],[-1892]],[[0,0],[0]],[[-40540,-688],[-688]],[[0,0],[0]],[[-61464,-86],[-86]],[[0]],[[-52696]],[[0]],[[-26786]],[[0]],[[-7972]],[[0]],[[-1282]],[[0]],[[-86]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
