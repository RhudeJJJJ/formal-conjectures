/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode043
import Proofs.RadenkovicGutmanD43Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,16641],[0,33282,-21156],[16641,-21156,6724]],[[0,0,0],[0,0,0],[0,0]],[[0,558441,-46182],[558441,-447342,29356],[-46182,29356]],[[0,0,0],[0,0,0],[0,0]],[[3749004,1352835,-298199],[1352835,-1948906,209920],[-298199,209920]],[[0,0,0],[0,0,0],[0,0]],[[19476288,-7247277,70466],[-7247277,-651270,246492],[70466,246492]],[[0,0,0],[0,0,0],[0,0]],[[-36507294,-35183312,2018320],[-35183312,7745828,100532],[2018320,100532]],[[0,0,0],[0,0,0],[0,0]],[[-591239826,-44993645,4045978],[-44993645,16533692,13448],[4045978,13448]],[[0,0,0],[0,0],[0]],[[-2302108170,38545935,3857645],[38545935,15848542],[3857645]],[[0,0,0],[0,0],[0]],[[-4939802440,203497292,2052598],[203497292,8391090],[2052598]],[[0,0,0],[0,0],[0]],[[-6527925226,315965719,622261],[315965719,2525526],[622261]],[[0,0,0],[0,0],[0]],[[-4995716000,285270145,100532],[285270145,404998],[100532]],[[0,0,0],[0,0],[0]],[[-939921876,168220232,6724],[168220232,26896],[6724]],[[0,0],[0]],[[2680830390,66865505],[66865505]],[[0,0],[0]],[[3782008282,17810061],[17810061]],[[0,0],[0]],[[2829379486,3052027],[3052027]],[[0,0],[0]],[[1422450438,304466],[304466]],[[0,0],[0]],[[508049364,13448],[13448]],[[0]],[[130001850]],[[0]],[[23388276]],[[0]],[[2815740]],[[0]],[[203934]],[[0]],[[6724]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
