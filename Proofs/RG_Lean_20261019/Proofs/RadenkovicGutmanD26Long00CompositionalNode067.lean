/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode043
import Proofs.RadenkovicGutmanD26Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,6084],[0,12168,-7488],[6084,-7488,2304]],[[0,0,0],[0,0,0],[0,0]],[[0,206388,-14664],[206388,-156336,9024],[-14664,9024]],[[0,0,0],[0,0,0],[0,0]],[[1408104,568404,-105980],[568404,-714808,70656],[-105980,70656]],[[0,0,0],[0,0,0],[0,0]],[[7927848,-2304612,2024],[-2304612,-382160,83904],[2024,83904]],[[0,0,0],[0,0,0],[0,0]],[[-7776648,-12559848,650160],[-12559848,2396064,34368],[650160,34368]],[[0,0,0],[0,0,0],[0,0]],[[-197548896,-18329060,1346344],[-18329060,5430992,4608],[1346344,4608]],[[0,0,0],[0,0],[0]],[[-811197664,6856660,1299876],[6856660,5305992],[1299876]],[[0,0,0],[0,0],[0]],[[-1802474608,61509008,696440],[61509008,2836816],[696440]],[[0,0,0],[0,0],[0]],[[-2485756584,101262876,212068],[101262876,859016],[212068]],[[0,0,0],[0,0],[0]],[[-2077815464,93673940,34368],[93673940,138336],[34368]],[[0,0,0],[0,0],[0]],[[-704361920,56010984,2304],[56010984,9216],[2304]],[[0,0],[0]],[[623931880,22470260],[22470260]],[[0,0],[0]],[[1125430760,6025372],[6025372]],[[0,0],[0]],[[895095312,1037884],[1037884]],[[0,0],[0]],[[463041600,103968],[103968]],[[0,0],[0]],[[168190464,4608],[4608]],[[0]],[[43524040]],[[0]],[[7894136]],[[0]],[[956280]],[[0]],[[69600]],[[0]],[[2304]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
