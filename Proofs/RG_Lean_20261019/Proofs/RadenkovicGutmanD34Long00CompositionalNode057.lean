/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode034
import Proofs.RadenkovicGutmanD34Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-102],[-102]],[[0,0],[0]],[[-1530,-442],[-442]],[[0,0],[0]],[[-10200,-544],[-544]],[[0,0],[0]],[[-26486,-238],[-238]],[[0,0],[0]],[[-35904,-34],[-34]],[[0]],[[-28152]],[[0]],[[-13192]],[[0]],[[-3638]],[[0]],[[-544]],[[0]],[[-34]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
