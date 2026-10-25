/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode100
import Proofs.RadenkovicGutmanD24Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,576]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-5184],[0,-10368,16992],[-5184,16992,48]],[[0,0,0],[0,0,0],[0,0]],[[-46656,-173664,61344],[-173664,326592,57216],[61344,57216]],[[0,0,0],[0,0,0],[0,0]],[[-2150064,425088,517392],[425088,2299968,62976],[517392,62976]],[[0,0,0],[0,0,0],[0,0]],[[-11555136,12140064,1469376],[12140064,6150720,26784],[1469376,26784]],[[0,0,0],[0,0,0],[0,0]],[[13731984,60130560,2153568],[60130560,8686080,4128],[2153568,4128]],[[0,0,0],[0,0,0],[0,0]],[[338205312,154701504,1828224],[154701504,7174656,96],[1828224,96]],[[0,0,0],[0,0],[0]],[[1539519696,248816640,930624],[248816640,3575808],[930624]],[[0,0,0],[0,0],[0]],[[3999454080,269308896,280896],[269308896,1061952],[280896]],[[0,0,0],[0,0],[0]],[[7008910752,202962912,46944],[202962912,175488],[46944]],[[0,0,0],[0,0],[0]],[[8852472000,107896416,3552],[107896416,13248],[3552]],[[0,0,0],[0,0],[0]],[[8331360384,40343904,48],[40343904,192],[48]],[[0,0],[0]],[[5946046080,10404000],[10404000]],[[0,0],[0]],[[3243089280,1770912],[1770912]],[[0,0],[0]],[[1351825152,181824],[181824]],[[0,0],[0]],[[427415376,9120],[9120]],[[0,0],[0]],[[100821888,96],[96]],[[0]],[[17227680]],[[0]],[[2025984]],[[0]],[[149136]],[[0]],[[5568]],[[0]],[[48]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
