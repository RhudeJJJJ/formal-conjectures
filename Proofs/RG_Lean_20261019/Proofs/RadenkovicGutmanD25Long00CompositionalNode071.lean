/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode043
import Proofs.RadenkovicGutmanD25Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e043 e066
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1875],[0,-1875,1150]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-16875,-28125],[-16875,-91800,19325],[-28125,19325,92]],[[0,0,0],[0,0,0],[0,0]],[[-413100,-1136700,-61725],[-1136700,-88344,76106],[-61725,76106]],[[0,0,0],[0,0,0],[0,0]],[[-13697748,-7795746,272002],[-7795746,1516860,86641],[272002,86641]],[[0,0,0],[0,0,0],[0,0]],[[-126767646,-21076852,1286419],[-21076852,5585336,37573],[1286419,37573]],[[0,0,0],[0,0,0],[0,0]],[[-597282516,-19855542,2220174],[-19855542,8841168,6022],[2220174,6022]],[[0,0,0],[0,0,0],[0,0]],[[-1717889088,28601462,2048425],[28601462,7740396,184],[2048425,184]],[[0,0,0],[0,0],[0]],[[-3244585028,112725004,1099262],[112725004,4004348],[1099262]],[[0,0,0],[0,0],[0]],[[-4081304980,166869775,345625],[166869775,1227104],[345625]],[[0,0,0],[0,0],[0]],[[-3196821186,149229407,60211],[149229407,210720],[60211]],[[0,0,0],[0,0],[0]],[[-962167774,88730119,4872],[88730119,17172],[4872]],[[0,0,0],[0,0],[0]],[[1069596454,36025680,92],[36025680,368],[92]],[[0,0],[0]],[[1795169440,9937265],[9937265]],[[0,0],[0]],[[1413275620,1800570],[1800570]],[[0,0],[0]],[[734953244,198395],[198395]],[[0,0],[0]],[[271121592,11150],[11150]],[[0,0],[0]],[[72000892,184],[184]],[[0]],[[13591670]],[[0]],[[1755070]],[[0]],[[143386]],[[0]],[[6278]],[[0]],[[92]]]
theorem step071 : p071=NestedArithmetic.mul p043 p066 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e043 e066 p043 p066 p071 rfl h043 h066 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
