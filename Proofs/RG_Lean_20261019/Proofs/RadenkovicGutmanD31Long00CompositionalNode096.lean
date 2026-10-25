/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode043
import Proofs.RadenkovicGutmanD31Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2883],[0,2883,-1798]],[[0,0,0],[0,0,0],[0,0]],[[0,25947,25947],[25947,106020,-19871],[25947,-19871]],[[0,0,0],[0,0,0],[0,0]],[[632772,1057968,35991],[1057968,163308,-70928],[35991,-70928]],[[0,0,0],[0,0,0],[0,0]],[[14573844,6255180,-275094],[6255180,-1034656,-72385],[-275094,-72385]],[[0,0,0],[0,0,0],[0,0]],[[115899390,14358022,-1020179],[14358022,-3967132,-27807],[-1020179,-27807]],[[0,0,0],[0,0,0],[0,0]],[[491483052,7873938,-1546404],[7873938,-6075504,-3596],[-1546404,-3596]],[[0,0,0],[0,0],[0]],[[1293017316,-32317624,-1286469],[-32317624,-5083876],[-1286469]],[[0,0,0],[0,0],[0]],[[2239943936,-89210250,-628866],[-89210250,-2495376],[-628866]],[[0,0,0],[0,0],[0]],[[2551074196,-116657867,-179769],[-116657867,-715604],[-179769]],[[0,0,0],[0,0],[0]],[[1697349262,-95746259,-27807],[-95746259,-110980],[-27807]],[[0,0,0],[0,0],[0]],[[153312298,-52923727,-1798],[-52923727,-7192],[-1798]],[[0,0],[0]],[[-1022642570,-20049870],[-20049870]],[[0,0],[0]],[[-1278898304,-5143551],[-5143551]],[[0,0],[0]],[[-901825960,-855042],[-855042]],[[0,0],[0]],[[-434921568,-83173],[-83173]],[[0,0],[0]],[[-150358308,-3596],[-3596]],[[0]],[[-37456060]],[[0]],[[-6587314]],[[0]],[[-777666]],[[0]],[[-55366]],[[0]],[[-1798]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
