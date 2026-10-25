/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode041
import Proofs.RadenkovicGutmanD28Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,84],[84,-52]],[[0,0],[0]],[[2052,-104],[-104]],[[0,0],[0]],[[11052,-800],[-800]],[[0,0],[0]],[[22668,-948],[-948]],[[0,0],[0]],[[19328,-388],[-388]],[[0,0],[0]],[[-144,-52],[-52]],[[0]],[[-13208]],[[0]],[[-10676]],[[0]],[[-3936]],[[0]],[[-716]],[[0]],[[-52]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
