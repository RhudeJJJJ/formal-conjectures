/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode177
import Proofs.RadenkovicGutmanD31Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-58],[0]],[[0,0],[0]],[[-986,0],[0,0]],[[0,0],[0,0]],[[-7076,0],[0,0]],[[0,0],[0,0]],[[-27898,0],[0,0]],[[0,0],[0,0]],[[-65888,0],[0,0]],[[0,0],[0,0]],[[-95352,-58],[-58,0]],[[0,0],[0,0]],[[-82940,-464],[-464,0]],[[0,0],[0,0]],[[-40426,-1276],[-1276,0]],[[0,0],[0,0]],[[-9222,-1392],[-1392,0]],[[0,0],[0,0]],[[-522,-522],[-522,0]],[[0],[0,0]],[[0],[0,-58]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
