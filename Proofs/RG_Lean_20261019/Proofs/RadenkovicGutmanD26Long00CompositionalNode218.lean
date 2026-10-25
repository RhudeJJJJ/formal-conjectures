/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode034
import Proofs.RadenkovicGutmanD26Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-26],[0]],[[0,0],[0]],[[-416,0],[0]],[[0,0],[0]],[[-2782,0],[0]],[[0,0],[0]],[[-10088,0],[0]],[[0,0],[0]],[[-21528,0],[0]],[[0,0],[0]],[[-27456,-26],[-26]],[[0,0],[0]],[[-20254,-182],[-182]],[[0,0],[0]],[[-7800,-416],[-416]],[[0,0],[0]],[[-1170,-338],[-338]],[[0,0],[0]],[[0,-78],[-78]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
