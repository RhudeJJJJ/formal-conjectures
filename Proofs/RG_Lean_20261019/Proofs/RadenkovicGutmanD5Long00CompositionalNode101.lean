/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode051
import Proofs.RadenkovicGutmanD5Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,25]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,600],[0,600,10]],[[0,0,0],[0,0,0],[0,0]],[[-2025,1350,3375],[1350,13680,2030],[3375,2030]],[[0,0,0],[0,0,0],[0,0]],[[-9990,92070,21060],[92070,85800,2380],[21060,2380]],[[0,0,0],[0,0,0],[0,0]],[[520695,774540,54720],[774540,224180,1190],[54720,1190]],[[0,0,0],[0,0,0],[0,0]],[[6245070,3031340,77570],[3031340,319440,260],[77570,260]],[[0,0,0],[0,0,0],[0,0]],[[33349835,7038660,65950],[7038660,272680,20],[65950,20]],[[0,0,0],[0,0],[0]],[[108101910,10725770,34810],[10725770,144240],[34810]],[[0,0,0],[0,0],[0]],[[238303150,11287600,11400],[11287600,47220],[11400]],[[0,0,0],[0,0],[0]],[[378663520,8423610,2230],[8423610,9200],[2230]],[[0,0,0],[0,0],[0]],[[448621780,4507370,235],[4507370,960],[235]],[[0,0,0],[0,0],[0]],[[404438120,1727100,10],[1727100,40],[10]],[[0,0],[0]],[[280692700,467200],[467200]],[[0,0],[0]],[[150742600,86450],[86450]],[[0,0],[0]],[[62601195,10300],[10300]],[[0,0],[0]],[[19971110,700],[700]],[[0,0],[0]],[[4827510,20],[20]],[[0]],[[863600]],[[0]],[[109975]],[[0]],[[9330]],[[0]],[[465]],[[0]],[[10]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
