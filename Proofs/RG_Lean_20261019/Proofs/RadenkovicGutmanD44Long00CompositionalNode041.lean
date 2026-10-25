/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode036
import Proofs.RadenkovicGutmanD44Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-84]],[[0,0],[0]],[[828,-756],[-756]],[[0,0],[0]],[[372,-2016],[-2016]],[[0,0],[0]],[[-11908,-1848],[-1848]],[[0,0],[0]],[[-39512,-672],[-672]],[[0,0],[0]],[[-59952,-84],[-84]],[[0]],[[-51424]],[[0]],[[-26148]],[[0]],[[-7784]],[[0]],[[-1252]],[[0]],[[-84]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
