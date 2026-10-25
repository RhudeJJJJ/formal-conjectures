/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode097
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e098 : NestedArithmetic.Expr 3 := .scaled (-1) e097
noncomputable def p098 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,972],[0,972]],[[0,0,0],[0,0,0],[0,0]],[[0,-8748,14580],[-8748,43740,4320],[14580,4320]],[[0,0,0],[0,0,0],[0,0]],[[-131220,289656,112752],[289656,324324,5652],[112752,5652]],[[0,0,0],[0,0,0],[0,0]],[[758160,3540996,347652],[3540996,958500,2844],[347652,2844]],[[0,0,0],[0,0,0],[0,0]],[[22329756,16696044,560844],[16696044,1491876,576],[560844,576]],[[0,0,0],[0,0,0],[0,0]],[[155688156,44114580,521028],[44114580,1348344,36],[521028,36]],[[0,0,0],[0,0],[0]],[[591255504,74144484,288252],[74144484,732024],[288252]],[[0,0,0],[0,0],[0]],[[1459316052,84163284,94428],[84163284,237492],[94428]],[[0,0,0],[0,0],[0]],[[2529994104,66490524,17316],[66490524,43668],[17316]],[[0,0,0],[0,0],[0]],[[3213603180,37003536,1512],[37003536,3924],[1512]],[[0,0,0],[0,0],[0]],[[3064909500,14474484,36],[14474484,108],[36]],[[0,0],[0]],[[2225310624,3909456],[3909456]],[[0,0],[0]],[[1237486032,700488],[700488]],[[0,0],[0]],[[526737060,76824],[76824]],[[0,0],[0]],[[170326152,4320],[4320]],[[0,0],[0]],[[41177700,72],[72]],[[0]],[[7237080]],[[0]],[[881460]],[[0]],[[68256]],[[0]],[[2808]],[[0]],[[36]]]
theorem step098 : p098=NestedHorner.scale (-1) p097 := by decide +kernel
#print axioms step098
theorem h098 : NestedArithmetic.compile e098=p098 := StagedExprCompile.compile_scaled (-1) e098 e097 p097 p098 rfl h097 step098
#print axioms h098
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
