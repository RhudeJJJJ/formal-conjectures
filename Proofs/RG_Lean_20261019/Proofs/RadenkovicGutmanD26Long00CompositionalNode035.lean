/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode034
import Proofs.RadenkovicGutmanD26Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-78],[-78]],[[0,0],[0]],[[-1404,-338],[-338]],[[0,0],[0]],[[-9828,-416],[-416]],[[0,0],[0]],[[-27144,-182],[-182]],[[0,0],[0]],[[-39364,-26],[-26]],[[0]],[[-33072]],[[0]],[[-16588]],[[0]],[[-4888]],[[0]],[[-780]],[[0]],[[-52]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
