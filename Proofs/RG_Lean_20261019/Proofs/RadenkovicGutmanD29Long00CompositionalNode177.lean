/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode174
import Proofs.RadenkovicGutmanD29Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-54],[0]],[[0,0],[0]],[[-918,0],[0,0]],[[0,0],[0,0]],[[-6588,0],[0,0]],[[0,0],[0,0]],[[-25974,0],[0,0]],[[0,0],[0,0]],[[-61344,0],[0,0]],[[0,0],[0,0]],[[-88776,-54],[-54,0]],[[0,0],[0,0]],[[-77220,-432],[-432,0]],[[0,0],[0,0]],[[-37638,-1188],[-1188,0]],[[0,0],[0,0]],[[-8586,-1296],[-1296,0]],[[0,0],[0,0]],[[-486,-486],[-486,0]],[[0],[0,0]],[[0],[0,-54]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
