/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode038
import Proofs.RadenkovicGutmanD17Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-15]],[[0,0],[0]],[[171,-135],[-135]],[[0,0],[0]],[[267,-360],[-360]],[[0,0],[0]],[[-1445,-330],[-330]],[[0,0],[0]],[[-5878,-120],[-120]],[[0,0],[0]],[[-9564,-15],[-15]],[[0]],[[-8540]],[[0]],[[-4461]],[[0]],[[-1354]],[[0]],[[-221]],[[0]],[[-15]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
