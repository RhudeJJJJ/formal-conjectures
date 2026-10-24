/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode034
import Proofs.RadenkovicGutmanD5Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-10],[0]],[[0,0],[0]],[[-150,0],[0]],[[0,0],[0]],[[-940,0],[0]],[[0,0],[0]],[[-3190,0],[0]],[[0,0],[0]],[[-6360,0],[0]],[[0,0],[0]],[[-7570,-5],[-5]],[[0,0],[0]],[[-5220,-35],[-35]],[[0,0],[0]],[[-1890,-80],[-80]],[[0,0],[0]],[[-270,-65],[-65]],[[0,0],[0]],[[0,-15],[-15]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
