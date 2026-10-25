/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode058
import Proofs.RadenkovicGutmanD12Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-20]],[[0,0],[0]],[[-180,-180],[-180]],[[0,0],[0]],[[-3180,-480],[-480]],[[0,0],[0]],[[-13940,-440],[-440]],[[0,0],[0]],[[-28600,-160],[-160]],[[0,0],[0]],[[-32880,-20],[-20]],[[0]],[[-22720]],[[0]],[[-9620]],[[0]],[[-2440]],[[0]],[[-340]],[[0]],[[-20]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
