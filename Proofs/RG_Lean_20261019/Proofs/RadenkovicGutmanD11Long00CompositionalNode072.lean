/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode051
import Proofs.RadenkovicGutmanD11Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e072 : NestedArithmetic.Expr 3 := .times e051 e061
noncomputable def p072 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,363],[0,363,-198]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-3267,5445],[-3267,16335,-3113],[5445,-3113,-36]],[[0,0,0],[0,0,0],[0,0]],[[-32967,97713,15609],[97713,14400,-13078],[15609,-13078]],[[0,0,0],[0,0,0],[0,0]],[[369225,608760,-31846],[608760,-295041,-15577],[-31846,-15577]],[[0,0,0],[0,0,0],[0,0]],[[4423248,312341,-200803],[312341,-1105212,-7249],[-200803,-7249]],[[0,0,0],[0,0,0],[0,0]],[[11052399,-6377944,-371306],[-6377944,-1796896,-1346],[-371306,-1346]],[[0,0,0],[0,0,0],[0,0]],[[-29154707,-24583643,-357393],[-24583643,-1622558,-72],[-357393,-72]],[[0,0,0],[0,0],[0]],[[-258816656,-46938598,-199426],[-46938598,-870209],[-199426]],[[0,0,0],[0,0],[0]],[[-811292772,-56150571,-65737],[-56150571,-279032],[-65737]],[[0,0,0],[0,0],[0]],[[-1563099553,-45347057,-12303],[-45347057,-51133],[-12303]],[[0,0,0],[0,0],[0]],[[-2093943910,-25457426,-1148],[-25457426,-4686],[-1148]],[[0,0,0],[0,0],[0]],[[-2053482084,-9996606,-36],[-9996606,-144],[-36]],[[0,0],[0]],[[-1512456172,-2712358],[-2712358]],[[0,0],[0]],[[-846882367,-491324],[-491324]],[[0,0],[0]],[[-361593551,-55360],[-55360]],[[0,0],[0]],[[-117141348,-3340],[-3340]],[[0,0],[0]],[[-28399656,-72],[-72]],[[0]],[[-5023195]],[[0]],[[-620473]],[[0]],[[-49537]],[[0]],[[-2192]],[[0]],[[-36]]]
theorem step072 : p072=NestedArithmetic.mul p051 p061 := by decide +kernel
#print axioms step072
theorem h072 : NestedArithmetic.compile e072=p072 := StagedExprCompile.compile_times e072 e051 e061 p051 p061 p072 rfl h051 h061 step072
#print axioms h072
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
