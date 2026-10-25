/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode058
import Proofs.RadenkovicGutmanD27Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-50]],[[0,0],[0]],[[-450,-450],[-450]],[[0,0],[0]],[[-7950,-1200],[-1200]],[[0,0],[0]],[[-34850,-1100],[-1100]],[[0,0],[0]],[[-71500,-400],[-400]],[[0,0],[0]],[[-82200,-50],[-50]],[[0]],[[-56800]],[[0]],[[-24050]],[[0]],[[-6100]],[[0]],[[-850]],[[0]],[[-50]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
