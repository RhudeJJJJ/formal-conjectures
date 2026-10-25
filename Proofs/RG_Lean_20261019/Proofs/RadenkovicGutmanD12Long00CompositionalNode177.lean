/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode174
import Proofs.RadenkovicGutmanD12Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-20],[0]],[[0,0],[0]],[[-340,0],[0,0]],[[0,0],[0,0]],[[-2440,0],[0,0]],[[0,0],[0,0]],[[-9620,0],[0,0]],[[0,0],[0,0]],[[-22720,0],[0,0]],[[0,0],[0,0]],[[-32880,-20],[-20,0]],[[0,0],[0,0]],[[-28600,-160],[-160,0]],[[0,0],[0,0]],[[-13940,-440],[-440,0]],[[0,0],[0,0]],[[-3180,-480],[-480,0]],[[0,0],[0,0]],[[-180,-180],[-180,0]],[[0],[0,0]],[[0],[0,-20]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
