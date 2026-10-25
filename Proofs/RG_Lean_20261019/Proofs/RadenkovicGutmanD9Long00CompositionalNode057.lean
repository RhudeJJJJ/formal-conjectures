/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode034
import Proofs.RadenkovicGutmanD9Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-27],[-27]],[[0,0],[0]],[[-405,-117],[-117]],[[0,0],[0]],[[-2700,-144],[-144]],[[0,0],[0]],[[-7011,-63],[-63]],[[0,0],[0]],[[-9504,-9],[-9]],[[0]],[[-7452]],[[0]],[[-3492]],[[0]],[[-963]],[[0]],[[-144]],[[0]],[[-9]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
