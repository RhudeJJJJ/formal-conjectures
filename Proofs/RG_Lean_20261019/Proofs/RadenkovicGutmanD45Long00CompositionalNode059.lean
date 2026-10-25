/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode058
import Proofs.RadenkovicGutmanD45Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-86]],[[0,0],[0]],[[-774,-774],[-774]],[[0,0],[0]],[[-13674,-2064],[-2064]],[[0,0],[0]],[[-59942,-1892],[-1892]],[[0,0],[0]],[[-122980,-688],[-688]],[[0,0],[0]],[[-141384,-86],[-86]],[[0]],[[-97696]],[[0]],[[-41366]],[[0]],[[-10492]],[[0]],[[-1462]],[[0]],[[-86]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
