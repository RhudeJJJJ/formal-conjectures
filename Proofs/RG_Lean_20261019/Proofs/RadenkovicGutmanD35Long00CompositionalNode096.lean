/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode043
import Proofs.RadenkovicGutmanD35Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3675],[0,3675,-2310]],[[0,0,0],[0,0,0],[0,0]],[[0,33075,33075],[33075,134820,-25655],[33075,-25655]],[[0,0,0],[0,0,0],[0,0]],[[805140,1345680,44415],[1345680,199500,-91280],[44415,-91280]],[[0,0,0],[0,0,0],[0,0]],[[18525780,7914060,-358470],[7914060,-1359680,-93065],[-358470,-93065]],[[0,0,0],[0,0,0],[0,0]],[[147055230,17930710,-1317995],[17930710,-5143740,-35735],[-1317995,-35735]],[[0,0,0],[0,0,0],[0,0]],[[622031340,8838690,-1992900],[8838690,-7847280,-4620],[-1992900,-4620]],[[0,0,0],[0,0],[0]],[[1630701940,-43570520,-1655885],[-43570520,-6553540],[-1655885]],[[0,0,0],[0,0],[0]],[[2809464000,-116856250,-808850],[-116856250,-3212720],[-808850]],[[0,0,0],[0,0],[0]],[[3166868180,-151592035,-231105],[-151592035,-920500],[-231105]],[[0,0,0],[0,0],[0]],[[2047288670,-123935595,-35735],[-123935595,-142660],[-35735]],[[0,0,0],[0,0],[0]],[[75095930,-68343975,-2310],[-68343975,-9240],[-2310]],[[0,0],[0]],[[-1399071450,-25849950],[-25849950]],[[0,0],[0]],[[-1688848000,-6623575],[-6623575]],[[0,0],[0]],[[-1177461320,-1100050],[-1100050]],[[0,0],[0]],[[-564648560,-106925],[-106925]],[[0,0],[0]],[[-194541060,-4620],[-4620]],[[0]],[[-48351100]],[[0]],[[-8489250]],[[0]],[[-1000930]],[[0]],[[-71190]],[[0]],[[-2310]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
