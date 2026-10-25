/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode036
import Proofs.RadenkovicGutmanD17Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-30]],[[0,0],[0]],[[342,-270],[-270]],[[0,0],[0]],[[534,-720],[-720]],[[0,0],[0]],[[-2890,-660],[-660]],[[0,0],[0]],[[-11756,-240],[-240]],[[0,0],[0]],[[-19128,-30],[-30]],[[0]],[[-17080]],[[0]],[[-8922]],[[0]],[[-2708]],[[0]],[[-442]],[[0]],[[-30]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
