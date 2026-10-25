/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode058
import Proofs.RadenkovicGutmanD8Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-12]],[[0,0],[0]],[[-108,-108],[-108]],[[0,0],[0]],[[-1908,-288],[-288]],[[0,0],[0]],[[-8364,-264],[-264]],[[0,0],[0]],[[-17160,-96],[-96]],[[0,0],[0]],[[-19728,-12],[-12]],[[0]],[[-13632]],[[0]],[[-5772]],[[0]],[[-1464]],[[0]],[[-204]],[[0]],[[-12]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
