/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode058
import Proofs.RadenkovicGutmanD29Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-54]],[[0,0],[0]],[[-486,-486],[-486]],[[0,0],[0]],[[-8586,-1296],[-1296]],[[0,0],[0]],[[-37638,-1188],[-1188]],[[0,0],[0]],[[-77220,-432],[-432]],[[0,0],[0]],[[-88776,-54],[-54]],[[0]],[[-61344]],[[0]],[[-25974]],[[0]],[[-6588]],[[0]],[[-918]],[[0]],[[-54]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
