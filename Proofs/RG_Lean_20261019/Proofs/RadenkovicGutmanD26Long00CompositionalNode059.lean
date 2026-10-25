/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode058
import Proofs.RadenkovicGutmanD26Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-48]],[[0,0],[0]],[[-432,-432],[-432]],[[0,0],[0]],[[-7632,-1152],[-1152]],[[0,0],[0]],[[-33456,-1056],[-1056]],[[0,0],[0]],[[-68640,-384],[-384]],[[0,0],[0]],[[-78912,-48],[-48]],[[0]],[[-54528]],[[0]],[[-23088]],[[0]],[[-5856]],[[0]],[[-816]],[[0]],[[-48]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
