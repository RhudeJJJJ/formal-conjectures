/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode034
import Proofs.RadenkovicGutmanD8Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-24],[-24]],[[0,0],[0]],[[-360,-104],[-104]],[[0,0],[0]],[[-2400,-128],[-128]],[[0,0],[0]],[[-6232,-56],[-56]],[[0,0],[0]],[[-8448,-8],[-8]],[[0]],[[-6624]],[[0]],[[-3104]],[[0]],[[-856]],[[0]],[[-128]],[[0]],[[-8]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
