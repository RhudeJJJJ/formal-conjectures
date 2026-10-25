/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode113
import Proofs.RadenkovicGutmanD29Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,841]],[[0,0],[0,0,0],[0,0]],[[0,0,7569],[0,0,15138],[7569,15138]],[[0,0,0],[0,0,0],[0,0]],[[68121,136242,133719],[136242,272484,40368],[133719,40368]],[[0,0,0],[0,0,0],[0,0]],[[2406942,2770254,586177],[2770254,1453248,37004],[586177,37004]],[[0,0,0],[0,0,0],[0,0]],[[31812507,17302734,1202630],[17302734,3269808,13456],[1202630,13456]],[[0,0,0],[0,0,0],[0,0]],[[208051626,55788576,1382604],[55788576,4036800,1682],[1382604,1682]],[[0,0,0],[0,0],[0]],[[815888581,110559542,955376],[110559542,2980504],[955376]],[[0,0,0],[0,0],[0]],[[2133331060,146123750,404521],[146123750,1345600],[404521]],[[0,0,0],[0,0],[0]],[[3958201822,134388436,102602],[134388436,363312],[102602]],[[0,0,0],[0,0],[0]],[[5416526098,87827312,14297],[87827312,53824],[14297]],[[0,0,0],[0,0],[0]],[[5602163392,41032390,841],[41032390,3364],[841]],[[0,0],[0]],[[4445795120,13598970],[13598970]],[[0,0],[0]],[[2729011360,3120110],[3120110]],[[0,0],[0]],[[1298488862,470960],[470960]],[[0,0],[0]],[[477100141,42050],[42050]],[[0,0],[0]],[[133951116,1682],[1682]],[[0]],[[28181910]],[[0]],[[4297510]],[[0]],[[448253]],[[0]],[[28594]],[[0]],[[841]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
