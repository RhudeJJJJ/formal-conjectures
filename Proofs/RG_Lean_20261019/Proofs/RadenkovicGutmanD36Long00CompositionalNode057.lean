/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode034
import Proofs.RadenkovicGutmanD36Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-108],[-108]],[[0,0],[0]],[[-1620,-468],[-468]],[[0,0],[0]],[[-10800,-576],[-576]],[[0,0],[0]],[[-28044,-252],[-252]],[[0,0],[0]],[[-38016,-36],[-36]],[[0]],[[-29808]],[[0]],[[-13968]],[[0]],[[-3852]],[[0]],[[-576]],[[0]],[[-36]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
