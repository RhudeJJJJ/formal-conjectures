/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode034
import Proofs.RadenkovicGutmanD21Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-21],[0]],[[0,0],[0]],[[-336,0],[0]],[[0,0],[0]],[[-2247,0],[0]],[[0,0],[0]],[[-8148,0],[0]],[[0,0],[0]],[[-17388,0],[0]],[[0,0],[0]],[[-22176,-21],[-21]],[[0,0],[0]],[[-16359,-147],[-147]],[[0,0],[0]],[[-6300,-336],[-336]],[[0,0],[0]],[[-945,-273],[-273]],[[0,0],[0]],[[0,-63],[-63]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
