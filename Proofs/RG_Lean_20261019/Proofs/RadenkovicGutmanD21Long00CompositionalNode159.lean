/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode037
import Proofs.RadenkovicGutmanD21Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-19],[0]],[[0,0],[0]],[[-285,0],[0,0]],[[0,0],[0,0]],[[-1786,0],[0,0]],[[0,0],[0,0]],[[-6061,0],[0,0]],[[0,0],[0,0]],[[-12084,0],[0,0]],[[0,0],[0,0]],[[-14364,-19],[-19,0]],[[0,0],[0,0]],[[-9766,-152],[-152,0]],[[0,0],[0,0]],[[-3173,-418],[-418,0]],[[0,0],[0,0]],[[-57,-456],[-456,0]],[[0,0],[0,0]],[[171,-171],[-171,0]],[[0],[0,0]],[[0],[0,-19]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
