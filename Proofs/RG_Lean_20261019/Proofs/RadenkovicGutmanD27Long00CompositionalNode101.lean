/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode051
import Proofs.RadenkovicGutmanD27Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,729]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,17496],[0,17496,54]],[[0,0,0],[0,0,0],[0,0]],[[-59049,39366,98415],[39366,394632,54918],[98415,54918]],[[0,0,0],[0,0,0],[0,0]],[[-310554,2646270,594864],[2646270,2387880,57996],[594864,57996]],[[0,0,0],[0,0,0],[0,0]],[[14503455,21802932,1492992],[21802932,6000588,24246],[1492992,24246]],[[0,0,0],[0,0,0],[0,0]],[[173118546,83505492,2030994],[83505492,8173440,3780],[2030994,3780]],[[0,0,0],[0,0,0],[0,0]],[[913702275,189485892,1637982],[189485892,6599880,108],[1637982,108]],[[0,0,0],[0,0],[0]],[[2921746194,281528082,804546],[281528082,3245184],[804546]],[[0,0,0],[0,0],[0]],[[6346209438,287863416,237384],[287863416,958284],[237384]],[[0,0,0],[0,0],[0]],[[9923553864,207664938,39366],[207664938,158976],[39366]],[[0,0,0],[0,0],[0]],[[11551529772,106621866,3051],[106621866,12312],[3051]],[[0,0,0],[0,0],[0]],[[10210687848,38769732,54],[38769732,216],[54]],[[0,0],[0]],[[6928969500,9781560],[9781560]],[[0,0],[0]],[[3624651720,1639386],[1639386]],[[0,0],[0]],[[1458600723,167292],[167292]],[[0,0],[0]],[[447566850,8532],[8532]],[[0,0],[0]],[[102926214,108],[108]],[[0]],[[17220600]],[[0]],[[1992735]],[[0]],[[145422]],[[0]],[[5481]],[[0]],[[54]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
