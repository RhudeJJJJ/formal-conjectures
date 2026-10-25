/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode177
import Proofs.RadenkovicGutmanD12Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-20],[0]],[[0,0],[0]],[[-340,0],[0,0]],[[0,0],[0,0]],[[-2440,0],[0,0]],[[0,0],[0,0]],[[-9620,0],[0,0]],[[0,0],[0,0]],[[-22720,0],[0,0]],[[0,0],[0,0]],[[-32880,-20],[-20,0]],[[0,0],[0,0]],[[-28600,-160],[-160,0]],[[0,0],[0,0]],[[-13940,-440],[-440,0]],[[0,0],[0,0]],[[-3180,-480],[-480,0]],[[0,0],[0,0]],[[-180,-180],[-180,0]],[[0],[0,0]],[[0],[0,-20]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
