/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode059
import Proofs.RadenkovicGutmanD28Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,84],[84,-52]],[[0,0],[0]],[[792,-104],[-104]],[[0,0],[0]],[[132,-800],[-800]],[[0,0],[0]],[[-14432,-948],[-948]],[[0,0],[0]],[[-44792,-388],[-388]],[[0,0],[0]],[[-62304,-52],[-52]],[[0]],[[-48208]],[[0]],[[-22016]],[[0]],[[-5896]],[[0]],[[-856]],[[0]],[[-52]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
