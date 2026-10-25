/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode043
import Proofs.RadenkovicGutmanD19Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1083],[0,1083,-646]],[[0,0,0],[0,0,0],[0,0]],[[0,9747,9747],[9747,40356,-6935],[9747,-6935]],[[0,0,0],[0,0,0],[0,0]],[[240084,402192,15903],[402192,75468,-25232],[15903,-25232]],[[0,0,0],[0,0,0],[0,0]],[[5558868,2446668,-90630],[2446668,-322240,-25897],[-90630,-25897]],[[0,0,0],[0,0,0],[0,0]],[[44650494,5998870,-354635],[5998870,-1348924,-9975],[-354635,-9975]],[[0,0,0],[0,0,0],[0,0]],[[191903724,4909410,-545604],[4909410,-2114928,-1292],[-545604,-1292]],[[0,0,0],[0,0],[0]],[[514263348,-8272600,-457197],[-8272600,-1790788],[-457197]],[[0,0,0],[0,0],[0]],[[916062656,-28400250,-224466],[-28400250,-885552],[-224466]],[[0,0,0],[0,0],[0]],[[1096775380,-39121475,-64353],[-39121475,-255284],[-64353]],[[0,0,0],[0,0],[0]],[[827087518,-32894795,-9975],[-32894795,-39748],[-9975]],[[0,0,0],[0,0],[0]],[[253563322,-18445447,-646],[-18445447,-2584],[-646]],[[0,0],[0]],[[-228635930,-7056030],[-7056030]],[[0,0],[0]],[[-384953984,-1823031],[-1823031]],[[0,0],[0]],[[-293348296,-304722],[-304722]],[[0,0],[0]],[[-146688816,-29773],[-29773]],[[0,0],[0]],[[-51796356,-1292],[-1292]],[[0]],[[-13084540]],[[0]],[[-2324194]],[[0]],[[-276450]],[[0]],[[-19798]],[[0]],[[-646]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
