/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode034
import Proofs.RadenkovicGutmanD25Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-75],[-75]],[[0,0],[0]],[[-1125,-325],[-325]],[[0,0],[0]],[[-7500,-400],[-400]],[[0,0],[0]],[[-19475,-175],[-175]],[[0,0],[0]],[[-26400,-25],[-25]],[[0]],[[-20700]],[[0]],[[-9700]],[[0]],[[-2675]],[[0]],[[-400]],[[0]],[[-25]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
