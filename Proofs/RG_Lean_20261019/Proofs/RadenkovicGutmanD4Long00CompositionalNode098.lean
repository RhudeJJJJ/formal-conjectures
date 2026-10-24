/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode095
import Proofs.RadenkovicGutmanD4Long00CompositionalNode097
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e098 : NestedArithmetic.Expr 3 := .plus e095 e097
noncomputable def p098 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,96],[0,96,-16]],[[0,0,0],[0,0,0],[0,0]],[[0,0,1152],[0,4176,152],[1152,152]],[[0,0,0],[0,0,0],[0,0]],[[5184,34344,7464],[34344,26040,-152],[7464,-152]],[[0,0,0],[0,0,0],[0,0]],[[322488,331128,19784],[331128,65792,-352],[19784,-352]],[[0,0,0],[0,0,0],[0,0]],[[3620808,1400544,27504],[1400544,85912,-168],[27504,-168]],[[0,0,0],[0,0,0],[0,0]],[[19854192,3427896,21416],[3427896,60688,-24],[21416,-24]],[[0,0,0],[0,0],[0]],[[66776344,5396880,9120],[5396880,20928],[9120]],[[0,0,0],[0,0],[0]],[[152307320,5746024,1752],[5746024,1120],[1752]],[[0,0,0],[0,0],[0]],[[248738480,4229776,-48],[4229776,-1512],[-48]],[[0,0,0],[0,0],[0]],[[300309456,2158008,-72],[2158008,-448],[-72]],[[0,0,0],[0,0],[0]],[[273132056,749112,-8],[749112,-40],[-8]],[[0,0],[0]],[[188963392,167696],[167696]],[[0,0],[0]],[[99665664,20816],[20816]],[[0,0],[0]],[[39860848,560],[560]],[[0,0],[0]],[[11910856,-176],[-176]],[[0,0],[0]],[[2581944,-16],[-16]],[[0]],[[383120]],[[0]],[[33936]],[[0]],[[968]],[[0]],[[-104]],[[0]],[[-8]]]
theorem step098 : p098=NestedHorner.add p095 p097 := by decide +kernel
#print axioms step098
theorem h098 : NestedArithmetic.compile e098=p098 := StagedExprCompile.compile_plus e098 e095 e097 p095 p097 p098 rfl h095 h097 step098
#print axioms h098
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
