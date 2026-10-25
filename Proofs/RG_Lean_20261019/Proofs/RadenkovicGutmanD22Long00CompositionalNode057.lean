/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode034
import Proofs.RadenkovicGutmanD22Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-66],[-66]],[[0,0],[0]],[[-990,-286],[-286]],[[0,0],[0]],[[-6600,-352],[-352]],[[0,0],[0]],[[-17138,-154],[-154]],[[0,0],[0]],[[-23232,-22],[-22]],[[0]],[[-18216]],[[0]],[[-8536]],[[0]],[[-2354]],[[0]],[[-352]],[[0]],[[-22]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
