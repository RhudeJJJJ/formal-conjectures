/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode217
import Proofs.RadenkovicGutmanD6Long00CompositionalNode186
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e266 : NestedArithmetic.Expr 3 := .times e217 e186
noncomputable def p266 : NestedHorner.Poly 3 := [[[96],[0],[0]],[[0,0],[0,0],[0]],[[3000,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[42984,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[374136,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2209536,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[9364848,144,0],[144,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[29379408,3252,0],[3252,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[69332952,32580,0],[32580,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[123767064,190620,0],[190620,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[166446624,721416,0],[721416,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[166019784,1847052,48],[1847052,192,0],[48,0]],[[0,0,0],[0,0,0],[0,0]],[[118639272,3246372,684],[3246372,2808,0],[684,0]],[[0,0,0],[0,0,0],[0,0]],[[56129136,3878544,4008],[3878544,17040,0],[4008,0]],[[0,0,0],[0,0,0],[0,0]],[[13570128,3015612,12396],[3015612,55416,0],[12396,0]],[[0,0,0],[0,0,0],[0,0]],[[-1406592,1340820,21528],[1340820,104112,0],[21528,0]],[[0,0,0],[0,0,0],[0,0]],[[-2145528,163272,20352],[163272,113376,48],[20352,48]],[[0,0,0],[0,0,0],[0,0]],[[-620136,-139212,8568],[-139212,67248,336],[8568,336]],[[0,0,0],[0,0,0],[0,0]],[[-64152,-67716,-468],[-67716,17208,768],[-468,768]],[[0,0,0],[0,0,0],[0,0]],[[0,-9396,-1512],[-9396,-432,624],[-1512,624]],[[0,0,0],[0,0,0],[0,0]],[[0,0,-324],[0,-648,144],[-324,144]]]
theorem step266 : p266=NestedArithmetic.mul p217 p186 := by decide +kernel
#print axioms step266
theorem h266 : NestedArithmetic.compile e266=p266 := StagedExprCompile.compile_times e266 e217 e186 p217 p186 p266 rfl h217 h186 step266
#print axioms h266
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
