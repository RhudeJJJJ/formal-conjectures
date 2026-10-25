/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode035
import Proofs.RadenkovicGutmanD36Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-11664],[0,-23328,7344],[-11664,7344]],[[0,0,0],[0,0,0],[0,0]],[[0,-318816,-34992],[-318816,62208,31824],[-34992,31824]],[[0,0,0],[0,0,0],[0,0]],[[-1959552,-1660176,119232],[-1660176,1163808,39168],[119232,39168]],[[0,0,0],[0,0,0],[0,0]],[[-13693536,1468368,684288],[1468368,3924288,17136],[684288,17136]],[[0,0,0],[0,0,0],[0,0]],[[-101088,31519872,1277712],[31519872,6261696,2448],[1277712,2448]],[[0,0,0],[0,0],[0]],[[323984448,108192240,1232928],[108192240,5579712],[1232928]],[[0,0,0],[0,0],[0]],[[1647118368,199662192,675936],[199662192,2913696],[675936]],[[0,0,0],[0,0],[0]],[[4496688576,234329184,211968],[234329184,884160],[211968]],[[0,0,0],[0,0],[0]],[[8106062112,185900832,35424],[185900832,144288],[35424]],[[0,0,0],[0,0],[0]],[[10409906304,102088512,2448],[102088512,9792],[2448]],[[0,0],[0]],[[9886150944,38879856],[38879856]],[[0,0],[0]],[[7080744384,10080720],[10080720]],[[0,0],[0]],[[3858802272,1697760],[1697760]],[[0,0],[0]],[[1600964928,167472],[167472]],[[0,0],[0]],[[501848928,7344],[7344]],[[0]],[[116807616]],[[0]],[[19557216]],[[0]],[[2225664]],[[0]],[[154080]],[[0]],[[4896]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
