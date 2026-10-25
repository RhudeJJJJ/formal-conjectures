/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode110
import Proofs.RadenkovicGutmanD13Long00CompositionalNode111
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e112 : NestedArithmetic.Expr 3 := .plus e110 e111
noncomputable def p112 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,169]],[[0,0],[0,0,0],[0,0,0]],[[0,0,1521],[0,0,3354],[1521,3354,536]],[[0,0,0],[0,0,0],[0,0,0]],[[13689,30186,35763],[30186,66276,19424],[35763,19424,4]],[[0,0,0],[0,0,0],[0,0]],[[602910,783918,236401],[783918,558120,36252],[236401,36252]],[[0,0,0],[0,0,0],[0,0]],[[9889911,6577974,726630],[6577974,1889456,28872],[726630,28872]],[[0,0,0],[0,0,0],[0,0]],[[81054570,28281440,1243180],[28281440,3450920,9922],[1243180,9922]],[[0,0,0],[0,0,0],[0,0]],[[397368025,74043070,1284088],[74043070,3784648,1240],[1284088,1240]],[[0,0,0],[0,0,0],[0,0]],[[1292157132,128599854,829305],[128599854,2598016,8],[829305,8]],[[0,0,0],[0,0],[0]],[[2967695666,155355564,336270],[155355564,1121184],[336270]],[[0,0,0],[0,0],[0]],[[5011359442,134017904,83161],[134017904,295208],[83161]],[[0,0,0],[0,0],[0]],[[6388451680,83585862,11517],[83585862,43508],[11517]],[[0,0,0],[0,0],[0]],[[6255148616,37734114,704],[37734114,2824],[704]],[[0,0,0],[0,0],[0]],[[4754242928,12202526,4],[12202526,16],[4]],[[0,0],[0]],[[2819527502,2755656],[2755656]],[[0,0],[0]],[[1305023301,413410],[413410]],[[0,0],[0]],[[469081236,37282],[37282]],[[0,0],[0]],[[129482186,1584],[1584]],[[0,0],[0]],[[26914694,8],[8]],[[0]],[[4078061]],[[0]],[[426170]],[[0]],[[27701]],[[0]],[[880]],[[0]],[[4]]]
theorem step112 : p112=NestedHorner.add p110 p111 := by decide +kernel
#print axioms step112
theorem h112 : NestedArithmetic.compile e112=p112 := StagedExprCompile.compile_plus e112 e110 e111 p110 p111 p112 rfl h110 h111 step112
#print axioms h112
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
