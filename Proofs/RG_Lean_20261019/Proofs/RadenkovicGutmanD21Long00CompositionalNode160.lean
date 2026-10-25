/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode159
import Proofs.RadenkovicGutmanD21Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-19],[0]],[[0,0],[0]],[[-285,0],[0,0]],[[0,0],[0,0]],[[-1786,0],[0,0]],[[0,0],[0,0]],[[-6061,0],[0,0]],[[0,0],[0,0]],[[-12084,0],[0,0]],[[0,0],[0,0]],[[-14364,-19],[-19,0]],[[0,0],[0,0]],[[-9766,-152],[-152,0]],[[0,0],[0,0]],[[-3173,-418],[-418,0]],[[0,0],[0,0]],[[-57,-456],[-456,0]],[[0,0],[0,0]],[[171,-171],[-171,0]],[[0],[0,0]],[[0],[0,-19]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
