/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode034
import Proofs.RadenkovicGutmanD17Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-51],[-51]],[[0,0],[0]],[[-765,-221],[-221]],[[0,0],[0]],[[-5100,-272],[-272]],[[0,0],[0]],[[-13243,-119],[-119]],[[0,0],[0]],[[-17952,-17],[-17]],[[0]],[[-14076]],[[0]],[[-6596]],[[0]],[[-1819]],[[0]],[[-272]],[[0]],[[-17]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
