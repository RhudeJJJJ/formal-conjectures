/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode058
import Proofs.RadenkovicGutmanD35Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-66]],[[0,0],[0]],[[-594,-594],[-594]],[[0,0],[0]],[[-10494,-1584],[-1584]],[[0,0],[0]],[[-46002,-1452],[-1452]],[[0,0],[0]],[[-94380,-528],[-528]],[[0,0],[0]],[[-108504,-66],[-66]],[[0]],[[-74976]],[[0]],[[-31746]],[[0]],[[-8052]],[[0]],[[-1122]],[[0]],[[-66]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
