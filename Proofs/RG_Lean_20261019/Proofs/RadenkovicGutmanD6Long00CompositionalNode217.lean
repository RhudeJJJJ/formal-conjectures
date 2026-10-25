/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode034
import Proofs.RadenkovicGutmanD6Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-12],[0]],[[0,0],[0]],[[-180,0],[0]],[[0,0],[0]],[[-1128,0],[0]],[[0,0],[0]],[[-3828,0],[0]],[[0,0],[0]],[[-7632,0],[0]],[[0,0],[0]],[[-9084,-6],[-6]],[[0,0],[0]],[[-6264,-42],[-42]],[[0,0],[0]],[[-2268,-96],[-96]],[[0,0],[0]],[[-324,-78],[-78]],[[0,0],[0]],[[0,-18],[-18]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
