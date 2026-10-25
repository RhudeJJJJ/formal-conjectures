/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode043
import Proofs.RadenkovicGutmanD23Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,4761],[0,9522,-5796],[4761,-5796,1764]],[[0,0,0],[0,0,0],[0,0]],[[0,162081,-10902],[162081,-120462,6636],[-10902,6636]],[[0,0,0],[0,0,0],[0,0]],[[1111644,463995,-82079],[463995,-559546,53760],[-82079,53760]],[[0,0,0],[0,0,0],[0,0]],[[6414768,-1711557,-4174],[-1711557,-334310,64092],[-4174,64092]],[[0,0,0],[0,0,0],[0,0]],[[-4614894,-9732672,486960],[-9732672,1766628,26292],[486960,26292]],[[0,0,0],[0,0,0],[0,0]],[[-149573586,-14771525,1020298],[-14771525,4096412,3528],[1020298,3528]],[[0,0,0],[0,0],[0]],[[-626100970,3610375,989445],[3610375,4029582],[989445]],[[0,0,0],[0,0],[0]],[[-1407426280,44954732,531398],[44954732,2161810],[531398]],[[0,0,0],[0,0],[0]],[[-1966766106,75699519,162061],[75699519,656006],[162061]],[[0,0,0],[0,0],[0]],[[-1685350160,70651385,26292],[70651385,105798],[26292]],[[0,0,0],[0,0],[0]],[[-638606036,42455352,1764],[42455352,7056],[1764]],[[0,0],[0]],[[400833190,17087705],[17087705]],[[0,0],[0]],[[817060682,4592821],[4592821]],[[0,0],[0]],[[665804286,792547],[792547]],[[0,0],[0]],[[348118758,79506],[79506]],[[0,0],[0]],[[127221204,3528],[3528]],[[0]],[[33054250]],[[0]],[[6012356]],[[0]],[[729900]],[[0]],[[53214]],[[0]],[[1764]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
