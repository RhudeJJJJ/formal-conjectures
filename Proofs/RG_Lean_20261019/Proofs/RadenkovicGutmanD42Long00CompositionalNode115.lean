/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode113
import Proofs.RadenkovicGutmanD42Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1764]],[[0,0],[0,0,0],[0,0]],[[0,0,15876],[0,0,31752],[15876,31752]],[[0,0,0],[0,0,0],[0,0]],[[142884,285768,280476],[285768,571536,84672],[280476,84672]],[[0,0,0],[0,0,0],[0,0]],[[5048568,5810616,1229508],[5810616,3048192,77616],[1229508,77616]],[[0,0,0],[0,0,0],[0,0]],[[66726828,36292536,2522520],[36292536,6858432,28224],[2522520,28224]],[[0,0,0],[0,0,0],[0,0]],[[436388904,117016704,2900016],[117016704,8467200,3528],[2900016,3528]],[[0,0,0],[0,0],[0]],[[1711328724,231898968,2003904],[231898968,6251616],[2003904]],[[0,0,0],[0,0],[0]],[[4474668240,306495000,848484],[306495000,2822400],[848484]],[[0,0,0],[0,0],[0]],[[8302340088,281880144,215208],[281880144,762048],[215208]],[[0,0,0],[0,0],[0]],[[11361179592,184218048,29988],[184218048,112896],[29988]],[[0,0,0],[0,0],[0]],[[11750554368,86065560,1764],[86065560,7056],[1764]],[[0,0],[0]],[[9325068480,28523880],[28523880]],[[0,0],[0]],[[5724109440,6544440],[6544440]],[[0,0],[0]],[[2723584248,987840],[987840]],[[0,0],[0]],[[1000718964,88200],[88200]],[[0,0],[0]],[[280962864,3528],[3528]],[[0]],[[59111640]],[[0]],[[9014040]],[[0]],[[940212]],[[0]],[[59976]],[[0]],[[1764]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
