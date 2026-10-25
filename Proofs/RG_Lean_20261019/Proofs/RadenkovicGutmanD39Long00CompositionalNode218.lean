/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode034
import Proofs.RadenkovicGutmanD39Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-39],[0]],[[0,0],[0]],[[-624,0],[0]],[[0,0],[0]],[[-4173,0],[0]],[[0,0],[0]],[[-15132,0],[0]],[[0,0],[0]],[[-32292,0],[0]],[[0,0],[0]],[[-41184,-39],[-39]],[[0,0],[0]],[[-30381,-273],[-273]],[[0,0],[0]],[[-11700,-624],[-624]],[[0,0],[0]],[[-1755,-507],[-507]],[[0,0],[0]],[[0,-117],[-117]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
