/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode059
import Proofs.RadenkovicGutmanD23Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,69],[69,-42]],[[0,0],[0]],[[657,-79],[-79]],[[0,0],[0]],[[222,-640],[-640]],[[0,0],[0]],[[-11357,-763],[-763]],[[0,0],[0]],[[-35772,-313],[-313]],[[0,0],[0]],[[-50004,-42],[-42]],[[0]],[[-38788]],[[0]],[[-17741]],[[0]],[[-4756]],[[0]],[[-691]],[[0]],[[-42]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
