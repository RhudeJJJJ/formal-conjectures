/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode092
import Proofs.RadenkovicGutmanD29Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2088,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-18792,-18792,0],[-18792,-17574,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-490158,-208278,0],[-208278,-56956,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4762206,-980316,0],[-980316,-90886,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-25108896,-2588250,0],[-2588250,-76444,0],[0,0]],[[0,0,0],[0,0],[0]],[[-83400694,-4264972,0],[-4264972,-32248],[0]],[[0,0,0],[0,0],[0]],[[-188503074,-4597602,0],[-4597602,-4292],[0]],[[0,0,0],[0,0],[0]],[[-303018564,-3278392,0],[-3278392,1450],[0]],[[0,0,0],[0,0],[0]],[[-355287584,-1501852,0],[-1501852,580],[0]],[[0,0,0],[0,0],[0]],[[-307366186,-388832,0],[-388832,58],[0]],[[0,0],[0]],[[-195855908,-20242],[-20242]],[[0,0],[0]],[[-90046276,21460],[21460]],[[0,0],[0]],[[-28061560,7366],[7366]],[[0,0],[0]],[[-4705482,1044],[1044]],[[0,0],[0]],[[303398,58],[58]],[[0]],[[416556]],[[0]],[[119016]],[[0]],[[18386]],[[0]],[[1566]],[[0]],[[58]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
