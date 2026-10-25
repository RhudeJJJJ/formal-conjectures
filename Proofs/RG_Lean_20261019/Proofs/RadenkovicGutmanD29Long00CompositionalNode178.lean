/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode177
import Proofs.RadenkovicGutmanD29Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-54],[0]],[[0,0],[0]],[[-918,0],[0,0]],[[0,0],[0,0]],[[-6588,0],[0,0]],[[0,0],[0,0]],[[-25974,0],[0,0]],[[0,0],[0,0]],[[-61344,0],[0,0]],[[0,0],[0,0]],[[-88776,-54],[-54,0]],[[0,0],[0,0]],[[-77220,-432],[-432,0]],[[0,0],[0,0]],[[-37638,-1188],[-1188,0]],[[0,0],[0,0]],[[-8586,-1296],[-1296,0]],[[0,0],[0,0]],[[-486,-486],[-486,0]],[[0],[0,0]],[[0],[0,-54]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
