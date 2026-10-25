/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode034
import Proofs.RadenkovicGutmanD31Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-93],[-93]],[[0,0],[0]],[[-1395,-403],[-403]],[[0,0],[0]],[[-9300,-496],[-496]],[[0,0],[0]],[[-24149,-217],[-217]],[[0,0],[0]],[[-32736,-31],[-31]],[[0]],[[-25668]],[[0]],[[-12028]],[[0]],[[-3317]],[[0]],[[-496]],[[0]],[[-31]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
