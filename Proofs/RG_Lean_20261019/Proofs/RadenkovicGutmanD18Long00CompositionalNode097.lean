/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode051
import Proofs.RadenkovicGutmanD18Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-972],[0,-972]],[[0,0,0],[0,0,0],[0,0]],[[0,8748,-14580],[8748,-43740,-4320],[-14580,-4320]],[[0,0,0],[0,0,0],[0,0]],[[131220,-289656,-112752],[-289656,-324324,-5652],[-112752,-5652]],[[0,0,0],[0,0,0],[0,0]],[[-758160,-3540996,-347652],[-3540996,-958500,-2844],[-347652,-2844]],[[0,0,0],[0,0,0],[0,0]],[[-22329756,-16696044,-560844],[-16696044,-1491876,-576],[-560844,-576]],[[0,0,0],[0,0,0],[0,0]],[[-155688156,-44114580,-521028],[-44114580,-1348344,-36],[-521028,-36]],[[0,0,0],[0,0],[0]],[[-591255504,-74144484,-288252],[-74144484,-732024],[-288252]],[[0,0,0],[0,0],[0]],[[-1459316052,-84163284,-94428],[-84163284,-237492],[-94428]],[[0,0,0],[0,0],[0]],[[-2529994104,-66490524,-17316],[-66490524,-43668],[-17316]],[[0,0,0],[0,0],[0]],[[-3213603180,-37003536,-1512],[-37003536,-3924],[-1512]],[[0,0,0],[0,0],[0]],[[-3064909500,-14474484,-36],[-14474484,-108],[-36]],[[0,0],[0]],[[-2225310624,-3909456],[-3909456]],[[0,0],[0]],[[-1237486032,-700488],[-700488]],[[0,0],[0]],[[-526737060,-76824],[-76824]],[[0,0],[0]],[[-170326152,-4320],[-4320]],[[0,0],[0]],[[-41177700,-72],[-72]],[[0]],[[-7237080]],[[0]],[[-881460]],[[0]],[[-68256]],[[0]],[[-2808]],[[0]],[[-36]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
