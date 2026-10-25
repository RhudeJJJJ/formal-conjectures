/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode113
import Proofs.RadenkovicGutmanD30Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,900]],[[0,0],[0,0,0],[0,0]],[[0,0,8100],[0,0,16200],[8100,16200]],[[0,0,0],[0,0,0],[0,0]],[[72900,145800,143100],[145800,291600,43200],[143100,43200]],[[0,0,0],[0,0,0],[0,0]],[[2575800,2964600,627300],[2964600,1555200,39600],[627300,39600]],[[0,0,0],[0,0,0],[0,0]],[[34044300,18516600,1287000],[18516600,3499200,14400],[1287000,14400]],[[0,0,0],[0,0,0],[0,0]],[[222647400,59702400,1479600],[59702400,4320000,1800],[1479600,1800]],[[0,0,0],[0,0],[0]],[[873126900,118315800,1022400],[118315800,3189600],[1022400]],[[0,0,0],[0,0],[0]],[[2282994000,156375000,432900],[156375000,1440000],[432900]],[[0,0,0],[0,0],[0]],[[4235887800,143816400,109800],[143816400,388800],[109800]],[[0,0,0],[0,0],[0]],[[5796520200,93988800,15300],[93988800,57600],[15300]],[[0,0,0],[0,0],[0]],[[5995180800,43911000,900],[43911000,3600],[900]],[[0,0],[0]],[[4757688000,14553000],[14553000]],[[0,0],[0]],[[2920464000,3339000],[3339000]],[[0,0],[0]],[[1389583800,504000],[504000]],[[0,0],[0]],[[510570900,45000],[45000]],[[0,0],[0]],[[143348400,1800],[1800]],[[0]],[[30159000]],[[0]],[[4599000]],[[0]],[[479700]],[[0]],[[30600]],[[0]],[[900]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
