/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode034
import Proofs.RadenkovicGutmanD33Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-66],[0]],[[0,0],[0]],[[-990,0],[0]],[[0,0],[0]],[[-6204,0],[0]],[[0,0],[0]],[[-21054,0],[0]],[[0,0],[0]],[[-41976,0],[0]],[[0,0],[0]],[[-49962,-33],[-33]],[[0,0],[0]],[[-34452,-231],[-231]],[[0,0],[0]],[[-12474,-528],[-528]],[[0,0],[0]],[[-1782,-429],[-429]],[[0,0],[0]],[[0,-99],[-99]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
