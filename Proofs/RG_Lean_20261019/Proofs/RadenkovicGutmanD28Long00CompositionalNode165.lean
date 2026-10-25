/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode164
import Proofs.RadenkovicGutmanD28Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-52],[0]],[[0,0],[0]],[[-772,0],[0,0]],[[0,0],[0,0]],[[-4776,0],[0,0]],[[0,0],[0,0]],[[-15940,0],[0,0]],[[0,0],[0,0]],[[-31072,0],[0,0]],[[0,0],[0,0]],[[-35760,-52],[-52,0]],[[0,0],[0,0]],[[-23064,-416],[-416,0]],[[0,0],[0,0]],[[-6564,-1144],[-1144,0]],[[0,0],[0,0]],[[468,-1248],[-1248,0]],[[0,0],[0,0]],[[540,-468],[-468,0]],[[0],[0,0]],[[0],[0,-52]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
