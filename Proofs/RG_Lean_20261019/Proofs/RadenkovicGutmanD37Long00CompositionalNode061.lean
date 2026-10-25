/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode059
import Proofs.RadenkovicGutmanD37Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,111],[111,-70]],[[0,0],[0]],[[1035,-149],[-149]],[[0,0],[0]],[[-30,-1088],[-1088]],[[0,0],[0]],[[-19967,-1281],[-1281]],[[0,0],[0]],[[-61028,-523],[-523]],[[0,0],[0]],[[-84444,-70],[-70]],[[0]],[[-65164]],[[0]],[[-29711]],[[0]],[[-7948]],[[0]],[[-1153]],[[0]],[[-70]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
