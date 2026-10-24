/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode032
import Proofs.RadenkovicGutmanD3Long00StagedUNode060
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e087 : NestedArithmetic.Expr 3 := .times e032 e060
noncomputable def p087 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,27],[0,27,-6]],[[0,0,0],[0,0,0],[0,0]],[[0,-243,243],[-243,891,9],[243,9]],[[0,0,0],[0,0,0],[0,0]],[[-3159,2673,1215],[2673,4158,-144],[1215,-144]],[[0,0,0],[0,0,0],[0,0]],[[-14661,28836,2106],[28836,6039,-201],[2106,-201]],[[0,0,0],[0,0,0],[0,0]],[[38394,100107,981],[100107,-198,-87],[981,-87]],[[0,0,0],[0,0,0],[0,0]],[[472167,170370,-1476],[170370,-9900,-12],[-1476,-12]],[[0,0,0],[0,0],[0]],[[1659723,130239,-2445],[130239,-12030],[-2445]],[[0,0,0],[0,0],[0]],[[3174306,-36414,-1554],[-36414,-6945],[-1554]],[[0,0,0],[0,0],[0]],[[3440616,-190503,-513],[-190503,-2178],[-513]],[[0,0,0],[0,0],[0]],[[1292403,-213069,-87],[-213069,-357],[-87]],[[0,0,0],[0,0],[0]],[[-2194572,-136638,-6],[-136638,-24],[-6]],[[0,0],[0]],[[-4546596,-56610],[-56610]],[[0,0],[0]],[[-4524024,-15432],[-15432]],[[0,0],[0]],[[-2986755,-2682],[-2682]],[[0,0],[0]],[[-1408509,-270],[-270]],[[0,0],[0]],[[-484290,-12],[-12]],[[0]],[[-120924]],[[0]],[[-21399]],[[0]],[[-2547]],[[0]],[[-183]],[[0]],[[-6]]]
theorem step087 : p087=NestedArithmetic.mul p032 p060 := by decide +kernel
#print axioms step087
theorem h087 : NestedArithmetic.compile e087=p087 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e032) (NestedArithmetic.compile e060)=p087
  rw [h032,h060]
  exact step087.symm
#print axioms h087
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
