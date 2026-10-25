/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode043
import Proofs.RadenkovicGutmanD24Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e043 e066
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1728],[0,-1728,1056]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-15552,-25920],[-15552,-84672,17712],[-25920,17712,88]],[[0,0,0],[0,0,0],[0,0]],[[-381024,-1048464,-57456],[-1048464,-84240,69888],[-57456,69888]],[[0,0,0],[0,0,0],[0,0]],[[-12639240,-7207056,247464],[-7207056,1383552,79680],[247464,79680]],[[0,0,0],[0,0,0],[0,0]],[[-117080208,-19579248,1178208],[-19579248,5116208,34640],[1178208,34640]],[[0,0,0],[0,0,0],[0,0]],[[-552312504,-18829392,2037360],[-18829392,8112544,5584],[2037360,5584]],[[0,0,0],[0,0,0],[0,0]],[[-1591132080,25268448,1882176],[25268448,7111872,176],[1882176,176]],[[0,0,0],[0,0],[0]],[[-3012281384,102427856,1011328],[102427856,3684384],[1011328]],[[0,0,0],[0,0],[0]],[[-3804267872,152469104,318496],[152469104,1131184],[318496]],[[0,0,0],[0,0],[0]],[[-3006935024,136721776,55632],[136721776,194848],[55632]],[[0,0,0],[0,0],[0]],[[-950730224,81447248,4528],[81447248,15984],[4528]],[[0,0,0],[0,0],[0]],[[934921120,33123808,88],[33123808,352],[88]],[[0,0],[0]],[[1623949664,9152976],[9152976]],[[0,0],[0]],[[1288800448,1662176],[1662176]],[[0,0],[0]],[[672870896,183776],[183776]],[[0,0],[0]],[[248880472,10400],[10400]],[[0,0],[0]],[[66242208,176],[176]],[[0]],[[12532944]],[[0]],[[1622800]],[[0]],[[133112]],[[0]],[[5872]],[[0]],[[88]]]
theorem step071 : p071=NestedArithmetic.mul p043 p066 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e043 e066 p043 p066 p071 rfl h043 h066 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
