/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode034
import Proofs.RadenkovicGutmanD22Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-44],[0]],[[0,0],[0]],[[-660,0],[0]],[[0,0],[0]],[[-4136,0],[0]],[[0,0],[0]],[[-14036,0],[0]],[[0,0],[0]],[[-27984,0],[0]],[[0,0],[0]],[[-33308,-22],[-22]],[[0,0],[0]],[[-22968,-154],[-154]],[[0,0],[0]],[[-8316,-352],[-352]],[[0,0],[0]],[[-1188,-286],[-286]],[[0,0],[0]],[[0,-66],[-66]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
