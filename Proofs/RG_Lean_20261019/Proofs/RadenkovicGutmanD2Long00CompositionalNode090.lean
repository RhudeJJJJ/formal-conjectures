/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode087
import Proofs.RadenkovicGutmanD2Long00CompositionalNode089
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .plus e087 e089
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,24],[0,24,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,288],[0,972,116],[288,116]],[[0,0,0],[0,0,0],[0,0]],[[324,7992,2244],[7992,7416,180],[2244,180]],[[0,0,0],[0,0,0],[0,0]],[[59076,83592,7052],[83592,22908,120],[7052,120]],[[0,0,0],[0,0,0],[0,0]],[[747792,380988,11808],[380988,38072,36],[11808,36]],[[0,0,0],[0,0,0],[0,0]],[[4393596,1006136,11668],[1006136,37792,4],[11668,4]],[[0,0,0],[0,0],[0]],[[15636508,1722844,7096],[1722844,23384],[7096]],[[0,0,0],[0,0],[0]],[[37665856,2024584,2676],[2024584,9084],[2676]],[[0,0,0],[0,0],[0]],[[65171888,1683232,608],[1683232,2152],[608]],[[0,0,0],[0,0],[0]],[[83923028,1004556,76],[1004556,284],[76]],[[0,0,0],[0,0],[0]],[[82215456,431336,4],[431336,16],[4]],[[0,0],[0]],[[62088592,131924],[131924]],[[0,0],[0]],[[36388008,28004],[28004]],[[0,0],[0]],[[16567652,3916],[3916]],[[0,0],[0]],[[5833724,324],[324]],[[0,0],[0]],[[1571024,12],[12]],[[0]],[[317168]],[[0]],[[46412]],[[0]],[[4644]],[[0]],[[284]],[[0]],[[8]]]
theorem step090 : p090=NestedHorner.add p087 p089 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_plus e090 e087 e089 p087 p089 p090 rfl h087 h089 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
