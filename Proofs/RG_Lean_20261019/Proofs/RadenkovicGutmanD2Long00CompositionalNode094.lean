/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode042
import Proofs.RadenkovicGutmanD2Long00CompositionalNode051
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e042 e051
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,12],[0,12,0]],[[0,0,0],[0,0,0],[0,0]],[[0,108,108],[108,576,52],[108,52]],[[0,0,0],[0,0,0],[0,0]],[[3240,5616,756],[5616,4272,64],[756,64]],[[0,0,0],[0,0,0],[0,0]],[[82080,50688,2088],[50688,12592,28],[2088,28]],[[0,0,0],[0,0,0],[0,0]],[[765504,213736,3028],[213736,19440,4],[3028,4]],[[0,0,0],[0,0,0],[0,0]],[[3897120,529224,2544],[529224,17280,0],[2544,0]],[[0,0,0],[0,0],[0]],[[12642376,849328,1276],[849328,9104],[1276]],[[0,0,0],[0,0],[0]],[[28307424,929000,376],[929000,2800],[376]],[[0,0,0],[0,0],[0]],[[45841568,710324,60],[710324,464],[60]],[[0,0,0],[0,0],[0]],[[55265384,383028,4],[383028,32],[4]],[[0,0,0],[0,0],[0]],[[50490536,144852,0],[144852,0],[0]],[[0,0],[0]],[[35305560,37560],[37560]],[[0,0],[0]],[[18961664,6356],[6356]],[[0,0],[0]],[[7801264,632],[632]],[[0,0],[0]],[[2435320,28],[28]],[[0,0],[0]],[[566160,0],[0]],[[0]],[[94880]],[[0]],[[10824]],[[0]],[[752]],[[0]],[[24]],[[0]],[[0]]]
theorem step094 : p094=NestedArithmetic.mul p042 p051 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e042 e051 p042 p051 p094 rfl h042 h051 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
