/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode035
import Proofs.RadenkovicGutmanD6Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-324],[0,-648,144],[-324,144]],[[0,0,0],[0,0,0],[0,0]],[[0,-9396,-1512],[-9396,-432,624],[-1512,624]],[[0,0,0],[0,0,0],[0,0]],[[-64152,-67716,-468],[-67716,17208,768],[-468,768]],[[0,0,0],[0,0,0],[0,0]],[[-620136,-139212,8568],[-139212,67248,336],[8568,336]],[[0,0,0],[0,0,0],[0,0]],[[-2145528,163272,20352],[163272,113376,48],[20352,48]],[[0,0,0],[0,0],[0]],[[-1406592,1340820,21528],[1340820,104112],[21528]],[[0,0,0],[0,0],[0]],[[13570128,3015612,12396],[3015612,55416],[12396]],[[0,0,0],[0,0],[0]],[[56129136,3878544,4008],[3878544,17040],[4008]],[[0,0,0],[0,0],[0]],[[118639272,3246372,684],[3246372,2808],[684]],[[0,0,0],[0,0],[0]],[[166019784,1847052,48],[1847052,192],[48]],[[0,0],[0]],[[166446624,721416],[721416]],[[0,0],[0]],[[123767064,190620],[190620]],[[0,0],[0]],[[69332952,32580],[32580]],[[0,0],[0]],[[29379408,3252],[3252]],[[0,0],[0]],[[9364848,144],[144]],[[0]],[[2209536]],[[0]],[[374136]],[[0]],[[42984]],[[0]],[[3000]],[[0]],[[96]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
