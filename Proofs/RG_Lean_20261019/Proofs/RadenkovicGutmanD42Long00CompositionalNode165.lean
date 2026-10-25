/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode164
import Proofs.RadenkovicGutmanD42Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-80],[0]],[[0,0],[0]],[[-1192,0],[0,0]],[[0,0],[0,0]],[[-7408,0],[0,0]],[[0,0],[0,0]],[[-24872,0],[0,0]],[[0,0],[0,0]],[[-48880,0],[0,0]],[[0,0],[0,0]],[[-56928,-80],[-80,0]],[[0,0],[0,0]],[[-37456,-640],[-640,0]],[[0,0],[0,0]],[[-11240,-1760],[-1760,0]],[[0,0],[0,0]],[[384,-1920],[-1920,0]],[[0,0],[0,0]],[[792,-720],[-720,0]],[[0],[0,0]],[[0],[0,-80]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
