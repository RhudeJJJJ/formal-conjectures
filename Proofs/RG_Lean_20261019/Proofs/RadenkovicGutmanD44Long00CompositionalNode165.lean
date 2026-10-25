/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode164
import Proofs.RadenkovicGutmanD44Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-84],[0]],[[0,0],[0]],[[-1252,0],[0,0]],[[0,0],[0,0]],[[-7784,0],[0,0]],[[0,0],[0,0]],[[-26148,0],[0,0]],[[0,0],[0,0]],[[-51424,0],[0,0]],[[0,0],[0,0]],[[-59952,-84],[-84,0]],[[0,0],[0,0]],[[-39512,-672],[-672,0]],[[0,0],[0,0]],[[-11908,-1848],[-1848,0]],[[0,0],[0,0]],[[372,-2016],[-2016,0]],[[0,0],[0,0]],[[828,-756],[-756,0]],[[0],[0,0]],[[0],[0,-84]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
