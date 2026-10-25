/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode035
import Proofs.RadenkovicGutmanD11Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-1089],[0,-2178,594],[-1089,594]],[[0,0,0],[0,0,0],[0,0]],[[0,-30591,-4092],[-30591,2508,2574],[-4092,2574]],[[0,0,0],[0,0,0],[0,0]],[[-197802,-188001,5357],[-188001,85558,3168],[5357,3168]],[[0,0,0],[0,0,0],[0,0]],[[-1644786,-137907,47938],[-137907,302588,1386],[47938,1386]],[[0,0,0],[0,0,0],[0,0]],[[-3283038,1854622,96162],[1854622,492096,198],[96162,198]],[[0,0,0],[0,0],[0]],[[14350248,7558265,95678],[7558265,443212],[95678]],[[0,0,0],[0,0],[0]],[[104613168,14775167,53361],[14775167,233046],[53361]],[[0,0,0],[0,0],[0]],[[314750876,17858984,16918],[17858984,71060],[16918]],[[0,0,0],[0,0],[0]],[[594063162,14426907,2849],[14426907,11638],[2849]],[[0,0,0],[0,0],[0]],[[783775454,8020837,198],[8020837,792],[198]],[[0,0],[0]],[[757754844,3082156],[3082156]],[[0,0],[0]],[[549682034,804595],[804595]],[[0,0],[0]],[[302438422,136235],[136235]],[[0,0],[0]],[[126415828,13497],[13497]],[[0,0],[0]],[[39864528,594],[594]],[[0]],[[9324216]],[[0]],[[1567566]],[[0]],[[179014]],[[0]],[[12430]],[[0]],[[396]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
