/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode034
import Proofs.RadenkovicGutmanD44Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-132],[-132]],[[0,0],[0]],[[-1980,-572],[-572]],[[0,0],[0]],[[-13200,-704],[-704]],[[0,0],[0]],[[-34276,-308],[-308]],[[0,0],[0]],[[-46464,-44],[-44]],[[0]],[[-36432]],[[0]],[[-17072]],[[0]],[[-4708]],[[0]],[[-704]],[[0]],[[-44]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
