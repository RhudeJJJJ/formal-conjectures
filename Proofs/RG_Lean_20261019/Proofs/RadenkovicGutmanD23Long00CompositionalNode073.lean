/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode071
import Proofs.RadenkovicGutmanD23Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-28566,0],[-28566,-6417,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-486243,-543375,0],[-543375,-75072,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-9980091,-4381362,0],[-4381362,-357581,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-90699534,-19911767,0],[-19911767,-899484,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-485875989,-57104078,0],[-57104078,-1306768,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1722892395,-109647509,0],[-109647509,-1138178,0],[0,0]],[[0,0,0],[0,0],[0]],[[-4305190876,-146008002,0],[-146008002,-598253],[0]],[[0,0,0],[0,0],[0]],[[-7879287192,-137702012,0],[-137702012,-185104],[0]],[[0,0,0],[0,0],[0]],[[-10832206523,-92959054,0],[-92959054,-30981],[0]],[[0,0,0],[0,0],[0]],[[-11374407028,-44962815,0],[-44962815,-2162],[0]],[[0,0,0],[0,0],[0]],[[-9218144470,-15426330,0],[-15426330,0],[0]],[[0,0],[0]],[[-5796085652,-3660013],[-3660013]],[[0,0],[0]],[[-2828594579,-570446],[-570446]],[[0,0],[0]],[[-1066267051,-52509],[-52509]],[[0,0],[0]],[[-307035556,-2162],[-2162]],[[0,0],[0]],[[-66209180,0],[0]],[[0]],[[-10339949]],[[0]],[[-1103563]],[[0]],[[-71967]],[[0]],[[-2162]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
