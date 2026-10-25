/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode119
import Proofs.RadenkovicGutmanD44Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-84],[0]],[[0,0],[0]],[[-1252,0],[0,0]],[[0,0],[0,0]],[[-7784,0],[0,0]],[[0,0],[0,0]],[[-26148,0],[0,0]],[[0,0],[0,0]],[[-51424,0],[0,0]],[[0,0],[0,0]],[[-59952,-84],[-84,0]],[[0,0],[0,0]],[[-39512,-672],[-672,0]],[[0,0],[0,0]],[[-11908,-1848],[-1848,0]],[[0,0],[0,0]],[[372,-2016],[-2016,0]],[[0,0],[0,0]],[[828,-756],[-756,0]],[[0],[0,0]],[[0],[0,-84]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
