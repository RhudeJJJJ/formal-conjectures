/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode089
import Proofs.RadenkovicGutmanD42Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,10584],[0,10584,-3360]],[[0,0,0],[0,0,0],[0,0]],[[0,0,127008],[0,428652,-14364],[127008,-14364]],[[0,0,0],[0,0,0],[0,0]],[[415044,3479112,672084],[3479112,2000376,-103740],[672084,-103740]],[[0,0,0],[0,0,0],[0,0]],[[29953476,30150792,1340892],[30150792,3026268,-121800],[1340892,-121800]],[[0,0,0],[0,0,0],[0,0]],[[324060912,113704668,1064448],[113704668,218232,-49644],[1064448,-49644]],[[0,0,0],[0,0,0],[0,0]],[[1689043356,243439896,-158172],[243439896,-4548768,-6636],[-158172,-6636]],[[0,0,0],[0,0],[0]],[[5368321308,322392924,-916104],[322392924,-5869416],[-916104]],[[0,0,0],[0,0],[0]],[[11495771616,265684104,-699804],[265684104,-3513636],[-699804]],[[0,0,0],[0,0],[0]],[[17454408048,121683072,-252672],[121683072,-1134168],[-252672]],[[0,0,0],[0,0],[0]],[[19288608948,8861916,-45444],[8861916,-190596],[-45444]],[[0,0,0],[0,0],[0]],[[15650744256,-26052264,-3276],[-26052264,-13104],[-3276]],[[0,0],[0]],[[9235896432,-18007836],[-18007836]],[[0,0],[0]],[[3802737288,-6180636],[-6180636]],[[0,0],[0]],[[947467332,-1231524],[-1231524]],[[0,0],[0]],[[37327164,-135996],[-135996]],[[0,0],[0]],[[-75842256,-6468],[-6468]],[[0]],[[-34029072]],[[0]],[[-7944468]],[[0]],[[-1117116]],[[0]],[[-89796]],[[0]],[[-3192]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
