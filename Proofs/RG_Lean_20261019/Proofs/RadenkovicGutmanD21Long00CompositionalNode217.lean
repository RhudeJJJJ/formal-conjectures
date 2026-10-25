/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode034
import Proofs.RadenkovicGutmanD21Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-42],[0]],[[0,0],[0]],[[-630,0],[0]],[[0,0],[0]],[[-3948,0],[0]],[[0,0],[0]],[[-13398,0],[0]],[[0,0],[0]],[[-26712,0],[0]],[[0,0],[0]],[[-31794,-21],[-21]],[[0,0],[0]],[[-21924,-147],[-147]],[[0,0],[0]],[[-7938,-336],[-336]],[[0,0],[0]],[[-1134,-273],[-273]],[[0,0],[0]],[[0,-63],[-63]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
