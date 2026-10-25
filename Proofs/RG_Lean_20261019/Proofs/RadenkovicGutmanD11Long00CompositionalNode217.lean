/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode034
import Proofs.RadenkovicGutmanD11Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-22],[0]],[[0,0],[0]],[[-330,0],[0]],[[0,0],[0]],[[-2068,0],[0]],[[0,0],[0]],[[-7018,0],[0]],[[0,0],[0]],[[-13992,0],[0]],[[0,0],[0]],[[-16654,-11],[-11]],[[0,0],[0]],[[-11484,-77],[-77]],[[0,0],[0]],[[-4158,-176],[-176]],[[0,0],[0]],[[-594,-143],[-143]],[[0,0],[0]],[[0,-33],[-33]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
