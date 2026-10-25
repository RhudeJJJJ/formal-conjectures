/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode034
import Proofs.RadenkovicGutmanD22Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-66],[-66]],[[0,0],[0]],[[-1188,-286],[-286]],[[0,0],[0]],[[-8316,-352],[-352]],[[0,0],[0]],[[-22968,-154],[-154]],[[0,0],[0]],[[-33308,-22],[-22]],[[0]],[[-27984]],[[0]],[[-14036]],[[0]],[[-4136]],[[0]],[[-660]],[[0]],[[-44]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
