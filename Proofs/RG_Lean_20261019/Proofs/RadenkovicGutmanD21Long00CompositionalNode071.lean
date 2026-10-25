/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode043
import Proofs.RadenkovicGutmanD21Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e043 e066
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1323],[0,-1323,798]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-11907,-19845],[-11907,-65016,13293],[-19845,13293,76]],[[0,0,0],[0,0,0],[0,0]],[[-292572,-805140,-45549],[-805140,-72216,52818],[-45549,52818]],[[0,0,0],[0,0,0],[0,0]],[[-9719028,-5579442,180666],[-5579442,1019868,60537],[180666,60537]],[[0,0,0],[0,0,0],[0,0]],[[-90326718,-15414228,881883],[-15414228,3831320,26549],[881883,26549]],[[0,0,0],[0,0,0],[0,0]],[[-427947876,-15870198,1535766],[-15870198,6113392,4366],[1535766,4366]],[[0,0,0],[0,0,0],[0,0]],[[-1239921360,16353270,1425393],[16353270,5384844,152],[1425393,152]],[[0,0,0],[0,0],[0]],[[-2366785796,74409452,769366],[74409452,2803740],[769366]],[[0,0,0],[0,0],[0]],[[-3030454868,113102231,243697],[113102231,866560],[243697]],[[0,0,0],[0,0],[0]],[[-2469036242,102442543,42963],[102442543,150880],[42963]],[[0,0,0],[0,0],[0]],[[-903923486,61448759,3568],[61448759,12660],[3568]],[[0,0,0],[0,0],[0]],[[575775046,25140808,76],[25140808,304],[76]],[[0,0],[0]],[[1159151024,6990921],[6990921]],[[0,0],[0]],[[948827812,1279586],[1279586]],[[0,0],[0]],[[502718924,143171],[143171]],[[0,0],[0]],[[187764472,8294],[8294]],[[0,0],[0]],[[50379996,152],[152]],[[0]],[[9608934]],[[0]],[[1256206]],[[0]],[[104474]],[[0]],[[4726]],[[0]],[[76]]]
theorem step071 : p071=NestedArithmetic.mul p043 p066 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e043 e066 p043 p066 p071 rfl h043 h066 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
