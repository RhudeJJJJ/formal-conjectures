/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode119
import Proofs.RadenkovicGutmanD42Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-80],[0]],[[0,0],[0]],[[-1192,0],[0,0]],[[0,0],[0,0]],[[-7408,0],[0,0]],[[0,0],[0,0]],[[-24872,0],[0,0]],[[0,0],[0,0]],[[-48880,0],[0,0]],[[0,0],[0,0]],[[-56928,-80],[-80,0]],[[0,0],[0,0]],[[-37456,-640],[-640,0]],[[0,0],[0,0]],[[-11240,-1760],[-1760,0]],[[0,0],[0,0]],[[384,-1920],[-1920,0]],[[0,0],[0,0]],[[792,-720],[-720,0]],[[0],[0,0]],[[0],[0,-80]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
