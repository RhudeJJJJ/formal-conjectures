/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode034
import Proofs.RadenkovicGutmanD15Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-15],[0]],[[0,0],[0]],[[-240,0],[0]],[[0,0],[0]],[[-1605,0],[0]],[[0,0],[0]],[[-5820,0],[0]],[[0,0],[0]],[[-12420,0],[0]],[[0,0],[0]],[[-15840,-15],[-15]],[[0,0],[0]],[[-11685,-105],[-105]],[[0,0],[0]],[[-4500,-240],[-240]],[[0,0],[0]],[[-675,-195],[-195]],[[0,0],[0]],[[0,-45],[-45]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
