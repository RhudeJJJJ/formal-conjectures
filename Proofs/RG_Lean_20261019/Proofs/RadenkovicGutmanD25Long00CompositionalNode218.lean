/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode034
import Proofs.RadenkovicGutmanD25Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-25],[0]],[[0,0],[0]],[[-400,0],[0]],[[0,0],[0]],[[-2675,0],[0]],[[0,0],[0]],[[-9700,0],[0]],[[0,0],[0]],[[-20700,0],[0]],[[0,0],[0]],[[-26400,-25],[-25]],[[0,0],[0]],[[-19475,-175],[-175]],[[0,0],[0]],[[-7500,-400],[-400]],[[0,0],[0]],[[-1125,-325],[-325]],[[0,0],[0]],[[0,-75],[-75]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
