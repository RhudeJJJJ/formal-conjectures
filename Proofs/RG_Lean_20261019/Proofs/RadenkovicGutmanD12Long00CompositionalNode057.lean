/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode034
import Proofs.RadenkovicGutmanD12Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-36],[-36]],[[0,0],[0]],[[-540,-156],[-156]],[[0,0],[0]],[[-3600,-192],[-192]],[[0,0],[0]],[[-9348,-84],[-84]],[[0,0],[0]],[[-12672,-12],[-12]],[[0]],[[-9936]],[[0]],[[-4656]],[[0]],[[-1284]],[[0]],[[-192]],[[0]],[[-12]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
