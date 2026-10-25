/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode034
import Proofs.RadenkovicGutmanD39Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-78],[0]],[[0,0],[0]],[[-1170,0],[0]],[[0,0],[0]],[[-7332,0],[0]],[[0,0],[0]],[[-24882,0],[0]],[[0,0],[0]],[[-49608,0],[0]],[[0,0],[0]],[[-59046,-39],[-39]],[[0,0],[0]],[[-40716,-273],[-273]],[[0,0],[0]],[[-14742,-624],[-624]],[[0,0],[0]],[[-2106,-507],[-507]],[[0,0],[0]],[[0,-117],[-117]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
