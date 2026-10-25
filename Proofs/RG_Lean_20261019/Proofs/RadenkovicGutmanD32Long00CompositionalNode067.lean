/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode043
import Proofs.RadenkovicGutmanD32Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,9216],[0,18432,-11520],[9216,-11520,3600]],[[0,0,0],[0,0,0],[0,0]],[[0,311040,-23808],[311040,-242016,14880],[-23808,14880]],[[0,0,0],[0,0,0],[0,0]],[[2106000,807840,-162800],[807840,-1081600,111360],[-162800,111360]],[[0,0,0],[0,0,0],[0,0]],[[11426400,-3741984,19712],[-3741984,-477536,131520],[19712,131520]],[[0,0,0],[0,0,0],[0,0]],[[-15817680,-19262880,1046976],[-19262880,3938112,53760],[1046976,53760]],[[0,0,0],[0,0,0],[0,0]],[[-312849120,-26477312,2133760],[-26477312,8662400,7200],[2133760,7200]],[[0,0,0],[0,0],[0]],[[-1251595696,15460576,2047584],[15460576,8384448],[2047584]],[[0,0,0],[0,0],[0]],[[-2735309248,102269792,1093376],[102269792,4461472],[1093376]],[[0,0,0],[0,0],[0]],[[-3698637600,163482432,332224],[163482432,1347008],[332224]],[[0,0,0],[0,0],[0]],[[-2972958560,149428736,53760],[149428736,216480],[53760]],[[0,0,0],[0,0],[0]],[[-814105856,88743648,3600],[88743648,14400],[3600]],[[0,0],[0]],[[1196024320,35442080],[35442080]],[[0,0],[0]],[[1886564864,9472864],[9472864]],[[0,0],[0]],[[1454525280,1627648],[1627648]],[[0,0],[0]],[[741833424,162720],[162720]],[[0,0],[0]],[[267234240,7200],[7200]],[[0]],[[68775520]],[[0]],[[12424928]],[[0]],[[1500624]],[[0]],[[108960]],[[0]],[[3600]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
