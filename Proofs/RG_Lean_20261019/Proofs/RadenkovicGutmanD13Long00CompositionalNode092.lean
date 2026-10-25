/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode089
import Proofs.RadenkovicGutmanD13Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1014],[0,1014,-286]],[[0,0,0],[0,0,0],[0,0]],[[0,0,12168],[0,41067,-676],[12168,-676]],[[0,0,0],[0,0,0],[0,0]],[[36855,333801,67782],[333801,205218,-7982],[67782,-7982]],[[0,0,0],[0,0,0],[0,0]],[[2828007,2960334,147368],[2960334,365547,-9802],[147368,-9802]],[[0,0,0],[0,0,0],[0,0]],[[31107726,11473839,146250],[11473839,197990,-4056],[146250,-4056]],[[0,0,0],[0,0,0],[0,0]],[[164474583,25462788,41522],[25462788,-209092,-546],[41522,-546]],[[0,0,0],[0,0],[0]],[[530633441,35560681,-44538],[35560681,-389402],[-44538]],[[0,0,0],[0,0],[0]],[[1156009478,32155630,-46956],[32155630,-256269],[-46956]],[[0,0,0],[0,0],[0]],[[1792825112,18289778,-18642],[18289778,-86398],[-18642]],[[0,0,0],[0,0],[0]],[[2037315293,5488288,-3510],[5488288,-14885],[-3510]],[[0,0,0],[0,0],[0]],[[1719616782,-184873,-260],[-184873,-1040],[-260]],[[0,0],[0]],[[1078743198,-911118],[-911118]],[[0,0],[0]],[[495163864,-394121],[-394121]],[[0,0],[0]],[[158722577,-86372],[-86372]],[[0,0],[0]],[[30668677,-10049],[-10049]],[[0,0],[0]],[[947830,-494],[-494]],[[0]],[[-1401868]],[[0]],[[-457509]],[[0]],[[-73203]],[[0]],[[-6305]],[[0]],[[-234]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
