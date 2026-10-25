/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode092
import Proofs.RadenkovicGutmanD9Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-648,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5832,-5832,0],[-5832,-5454,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-152118,-64638,0],[-64638,-17676,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1477926,-304236,0],[-304236,-28206,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7792416,-803250,0],[-803250,-23724,0],[0,0]],[[0,0,0],[0,0],[0]],[[-25882974,-1323612,0],[-1323612,-10008],[0]],[[0,0,0],[0,0],[0]],[[-58500954,-1426842,0],[-1426842,-1332],[0]],[[0,0,0],[0,0],[0]],[[-94040244,-1017432,0],[-1017432,450],[0]],[[0,0,0],[0,0],[0]],[[-110261664,-466092,0],[-466092,180],[0]],[[0,0,0],[0,0],[0]],[[-95389506,-120672,0],[-120672,18],[0]],[[0,0],[0]],[[-60782868,-6282],[-6282]],[[0,0],[0]],[[-27945396,6660],[6660]],[[0,0],[0]],[[-8708760,2286],[2286]],[[0,0],[0]],[[-1460322,324],[324]],[[0,0],[0]],[[94158,18],[18]],[[0]],[[129276]],[[0]],[[36936]],[[0]],[[5706]],[[0]],[[486]],[[0]],[[18]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
