/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode034
import Proofs.RadenkovicGutmanD26Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-78],[-78]],[[0,0],[0]],[[-1170,-338],[-338]],[[0,0],[0]],[[-7800,-416],[-416]],[[0,0],[0]],[[-20254,-182],[-182]],[[0,0],[0]],[[-27456,-26],[-26]],[[0]],[[-21528]],[[0]],[[-10088]],[[0]],[[-2782]],[[0]],[[-416]],[[0]],[[-26]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
