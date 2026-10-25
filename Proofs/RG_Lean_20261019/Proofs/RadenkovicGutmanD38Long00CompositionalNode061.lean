/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode059
import Proofs.RadenkovicGutmanD38Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,114],[114,-72]],[[0,0],[0]],[[1062,-154],[-154]],[[0,0],[0]],[[-48,-1120],[-1120]],[[0,0],[0]],[[-20582,-1318],[-1318]],[[0,0],[0]],[[-62832,-538],[-538]],[[0,0],[0]],[[-86904,-72],[-72]],[[0]],[[-67048]],[[0]],[[-30566]],[[0]],[[-8176]],[[0]],[[-1186]],[[0]],[[-72]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
