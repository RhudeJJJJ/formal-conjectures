/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode119
import Proofs.RadenkovicGutmanD28Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-52],[0]],[[0,0],[0]],[[-772,0],[0,0]],[[0,0],[0,0]],[[-4776,0],[0,0]],[[0,0],[0,0]],[[-15940,0],[0,0]],[[0,0],[0,0]],[[-31072,0],[0,0]],[[0,0],[0,0]],[[-35760,-52],[-52,0]],[[0,0],[0,0]],[[-23064,-416],[-416,0]],[[0,0],[0,0]],[[-6564,-1144],[-1144,0]],[[0,0],[0,0]],[[468,-1248],[-1248,0]],[[0,0],[0,0]],[[540,-468],[-468,0]],[[0],[0,0]],[[0],[0,-52]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
