/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode070
import Proofs.RadenkovicGutmanD14Long00CompositionalNode082
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e083 : NestedArithmetic.Expr 3 := .plus e070 e082
noncomputable def p083 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,336],[0,336,632]],[[0,0,0],[0,0,0],[0,0,0]],[[0,3024,10080],[3024,24480,13168],[10080,13168,4]],[[0,0,0],[0,0,0],[0,0]],[[-12312,341280,136536],[341280,408432,33656],[136536,33656]],[[0,0,0],[0,0,0],[0,0]],[[2001132,4473936,560740],[4473936,1772816,30576],[560740,30576]],[[0,0,0],[0,0,0],[0,0]],[[32513832,23914552,1118352],[23914552,3654608,11184],[1118352,11184]],[[0,0,0],[0,0,0],[0,0]],[[219065484,70874928,1266400],[70874928,4262176,1440],[1266400,1440]],[[0,0,0],[0,0,0],[0,0]],[[856068280,132720832,867712],[132720832,3009536,8],[867712,8]],[[0,0,0],[0,0],[0]],[[2213096300,167965616,366104],[167965616,1309856],[366104]],[[0,0,0],[0,0],[0]],[[4055197456,149031944,93040],[149031944,343632],[93040]],[[0,0,0],[0,0],[0]],[[5485865656,94435696,13120],[94435696,50048],[13120]],[[0,0,0],[0,0],[0]],[[5618666496,42947600,808],[42947600,3184],[808]],[[0,0,0],[0,0],[0]],[[4423820752,13907376,4],[13907376,16],[4]],[[0,0],[0]],[[2699178032,3131128],[3131128]],[[0,0],[0]],[[1278863520,466704],[466704]],[[0,0],[0]],[[468746680,41680],[41680]],[[0,0],[0]],[[131543660,1744],[1744]],[[0,0],[0]],[[27729584,8],[8]],[[0]],[[4251832]],[[0]],[[448744]],[[0]],[[29388]],[[0]],[[936]],[[0]],[[4]]]
theorem step083 : p083=NestedHorner.add p070 p082 := by decide +kernel
#print axioms step083
theorem h083 : NestedArithmetic.compile e083=p083 := StagedExprCompile.compile_plus e083 e070 e082 p070 p082 p083 rfl h070 h082 step083
#print axioms h083
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
