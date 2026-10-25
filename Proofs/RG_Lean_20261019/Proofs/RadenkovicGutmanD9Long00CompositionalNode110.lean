/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode043
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e110 : NestedArithmetic.Expr 3 := .pow e043 2
noncomputable def p110 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,729],[0,1458,-756],[729,-756,196]],[[0,0,0],[0,0,0],[0,0]],[[0,36936,-486],[36936,-20124,252],[-486,252]],[[0,0,0],[0,0,0],[0,0]],[[467856,202824,-10287],[202824,-132126,5376],[-10287,5376]],[[0,0,0],[0,0,0],[0,0]],[[5450112,161244,-9774],[161244,-276532,6860],[-9774,6860]],[[0,0,0],[0,0,0],[0,0]],[[28427760,-1485144,35712],[-1485144,-211208,2884],[35712,2884]],[[0,0,0],[0,0,0],[0,0]],[[86938896,-5560644,95178],[-5560644,66708,392],[95178,392]],[[0,0,0],[0,0],[0]],[[170705764,-9355408,99829],[-9355408,232194],[99829]],[[0,0,0],[0,0],[0]],[[218882536,-8737912,55846],[-8737912,171220],[55846]],[[0,0,0],[0,0],[0]],[[170781748,-4066148,17469],[-4066148,61090],[17469]],[[0,0,0],[0,0],[0]],[[49602856,200312,2884],[200312,10920],[2884]],[[0,0,0],[0,0],[0]],[[-50676080,1518676,196],[1518676,784],[196]],[[0,0],[0]],[[-71812240,999060],[999060]],[[0,0],[0]],[[-39771236,347468],[347468]],[[0,0],[0]],[[-7279840,70916],[70916]],[[0,0],[0]],[[4782772,8036],[8036]],[[0,0],[0]],[[4275336,392],[392]],[[0]],[[1687260]],[[0]],[[403240]],[[0]],[[60008]],[[0]],[[5152]],[[0]],[[196]]]
theorem step110 : p110=NestedArithmetic.power p043 2 := by decide +kernel
#print axioms step110
theorem h110 : NestedArithmetic.compile e110=p110 := StagedExprCompile.compile_pow 2 e110 e043 p043 p110 rfl h043 step110
#print axioms h110
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
