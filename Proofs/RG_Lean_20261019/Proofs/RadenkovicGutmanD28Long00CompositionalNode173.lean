/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode165
import Proofs.RadenkovicGutmanD28Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-52],[0]],[[0,0],[0]],[[-716,0],[0,0]],[[0,0],[0,0]],[[-3936,0],[0,0]],[[0,0],[0,0]],[[-10676,0],[0,0]],[[0,0],[0,0]],[[-13208,0],[0,0]],[[0,0],[0,0]],[[-144,-52],[-52,0]],[[0,0],[0,0]],[[19328,-388],[-388,0]],[[0,0],[0,0]],[[22668,-948],[-948,0]],[[0,0],[0,0]],[[11052,-800],[-800,0]],[[0,0],[0,0]],[[2052,-104],[-104,0]],[[0,0],[0,0]],[[0,84],[84,-52]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
