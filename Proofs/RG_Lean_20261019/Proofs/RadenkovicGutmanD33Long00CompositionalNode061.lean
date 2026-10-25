/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode059
import Proofs.RadenkovicGutmanD33Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,99],[99,-62]],[[0,0],[0]],[[927,-129],[-129]],[[0,0],[0]],[[42,-960],[-960]],[[0,0],[0]],[[-17507,-1133],[-1133]],[[0,0],[0]],[[-53812,-463],[-463]],[[0,0],[0]],[[-74604,-62],[-62]],[[0]],[[-57628]],[[0]],[[-26291]],[[0]],[[-7036]],[[0]],[[-1021]],[[0]],[[-62]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
