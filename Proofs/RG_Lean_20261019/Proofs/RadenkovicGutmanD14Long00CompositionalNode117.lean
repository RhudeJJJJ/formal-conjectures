/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode112
import Proofs.RadenkovicGutmanD14Long00CompositionalNode116
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e117 : NestedArithmetic.Expr 3 := .plus e112 e116
noncomputable def p117 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,336],[0,336,632]],[[0,0,0],[0,0,0],[0,0,0]],[[0,3024,10080],[3024,12384,13168],[10080,13168,4]],[[0,0,0],[0,0,0],[0,0]],[[132840,253584,136536],[253584,304104,33656],[136536,33656]],[[0,0,0],[0,0,0],[0,0]],[[3922884,3519864,560740],[3519864,1421024,30576],[560740,30576]],[[0,0,0],[0,0,0],[0,0]],[[44336160,19509592,1118352],[19509592,3053896,11184],[1118352,11184]],[[0,0,0],[0,0,0],[0,0]],[[264906636,59439448,1266400],[59439448,3691088,1440],[1266400,1440]],[[0,0,0],[0,0,0],[0,0]],[[982939472,114049312,867712],[114049312,2698400,8],[867712,8]],[[0,0,0],[0,0],[0]],[[2478021716,147698824,366104],[147698824,1214992],[366104]],[[0,0,0],[0,0],[0]],[[4481656608,134018792,93040],[134018792,329352],[93040]],[[0,0,0],[0,0],[0]],[[6018809592,86806256,13120],[86806256,49488],[13120]],[[0,0,0],[0,0],[0]],[[6137056872,40333856,808],[40333856,3240],[808]],[[0,0,0],[0,0],[0]],[[4816849248,13336568,4],[13336568,16],[4]],[[0,0],[0]],[[2931506912,3063928],[3063928]],[[0,0],[0]],[[1385725184,465640],[465640]],[[0,0],[0]],[[506771744,42352],[42352]],[[0,0],[0]],[[141892404,1800],[1800]],[[0,0],[0]],[[29841344,8],[8]],[[0]],[[4564312]],[[0]],[[480384]],[[0]],[[31348]],[[0]],[[992]],[[0]],[[4]]]
theorem step117 : p117=NestedHorner.add p112 p116 := by decide +kernel
#print axioms step117
theorem h117 : NestedArithmetic.compile e117=p117 := StagedExprCompile.compile_plus e117 e112 e116 p112 p116 p117 rfl h112 h116 step117
#print axioms h117
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
