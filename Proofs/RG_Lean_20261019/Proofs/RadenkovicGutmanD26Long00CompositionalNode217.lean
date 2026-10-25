/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode034
import Proofs.RadenkovicGutmanD26Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-52],[0]],[[0,0],[0]],[[-780,0],[0]],[[0,0],[0]],[[-4888,0],[0]],[[0,0],[0]],[[-16588,0],[0]],[[0,0],[0]],[[-33072,0],[0]],[[0,0],[0]],[[-39364,-26],[-26]],[[0,0],[0]],[[-27144,-182],[-182]],[[0,0],[0]],[[-9828,-416],[-416]],[[0,0],[0]],[[-1404,-338],[-338]],[[0,0],[0]],[[0,-78],[-78]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
