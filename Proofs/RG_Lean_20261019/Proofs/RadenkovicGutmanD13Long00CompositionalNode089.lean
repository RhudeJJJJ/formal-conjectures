/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode033
import Proofs.RadenkovicGutmanD13Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,507],[0,507,-286]],[[0,0,0],[0,0,0],[0,0]],[[0,-4563,4563],[-4563,16731,-2951],[4563,-2951]],[[0,0,0],[0,0,0],[0,0]],[[-45279,50193,8775],[50193,21918,-11024],[8775,-11024]],[[0,0,0],[0,0,0],[0,0]],[[-31941,288756,-35334],[288756,-186121,-11401],[-35334,-11401]],[[0,0,0],[0,0,0],[0,0]],[[1465074,-141973,-150059],[-141973,-677638,-4407],[-150059,-4407]],[[0,0,0],[0,0,0],[0,0]],[[5330247,-4045470,-235716],[-4045470,-1017900,-572],[-235716,-572]],[[0,0,0],[0,0],[0]],[[-2534077,-12904801,-199485],[-12904801,-840190],[-199485]],[[0,0,0],[0,0],[0]],[[-64795614,-22071374,-98514],[-22071374,-407745],[-98514]],[[0,0,0],[0,0],[0]],[[-219585704,-24194183,-28353],[-24194183,-115778],[-28353]],[[0,0,0],[0,0],[0]],[[-428306957,-18088109,-4407],[-18088109,-17797],[-4407]],[[0,0,0],[0,0],[0]],[[-570605932,-9438078,-286],[-9438078,-1144],[-286]],[[0,0],[0]],[[-552704516,-3439410],[-3439410]],[[0,0],[0]],[[-400617464,-858312],[-858312]],[[0,0],[0]],[[-220078755,-139802],[-139802]],[[0,0],[0]],[[-91842309,-13390],[-13390]],[[0,0],[0]],[[-28920450,-572],[-572]],[[0]],[[-6756204]],[[0]],[[-1134679]],[[0]],[[-129467]],[[0]],[[-8983]],[[0]],[[-286]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
