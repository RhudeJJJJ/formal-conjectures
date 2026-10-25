/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode217
import Proofs.RadenkovicGutmanD19Long00CompositionalNode219
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e220 : NestedArithmetic.Expr 3 := .times e217 e219
noncomputable def p220 : NestedHorner.Poly 3 := [[[-722],[0],[0]],[[0,0],[0,0],[0]],[[-22382,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-318402,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-2755152,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-16206012,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-68600108,-1083,0],[-1083,0],[0]],[[0,0,0],[0,0],[0]],[[-215812298,-24187,0],[-24187,0],[0]],[[0,0,0],[0,0],[0]],[[-513839458,-240065,0],[-240065,0],[0]],[[0,0,0],[0,0],[0]],[[-934169808,-1395626,0],[-1395626,0],[0]],[[0,0,0],[0,0],[0]],[[-1298862838,-5273849,0],[-5273849,0],[0]],[[0,0,0],[0,0],[0]],[[-1374112566,-13594899,-361],[-13594899,-722],[-361]],[[0,0,0],[0,0],[0]],[[-1092427876,-24416596,-5054],[-24416596,-10108],[-5054]],[[0,0,0],[0,0],[0]],[[-638463156,-30662257,-29241],[-30662257,-58482],[-29241]],[[0,0,0],[0,0],[0]],[[-264546576,-26614003,-90250],[-26614003,-180500],[-90250]],[[0,0,0],[0,0],[0]],[[-73083006,-15504950,-160284],[-15504950,-320568],[-160284]],[[0,0,0],[0,0],[0]],[[-11988810,-5727987,-165338],[-5727987,-330676],[-165338]],[[0,0,0],[0,0],[0]],[[-877230,-1198881,-95665],[-1198881,-191330],[-95665]],[[0,0,0],[0,0],[0]],[[0,-107217,-28158],[-107217,-56316],[-28158]],[[0,0,0],[0,0],[0]],[[0,0,-3249],[0,-6498],[-3249]]]
theorem step220 : p220=NestedArithmetic.mul p217 p219 := by decide +kernel
#print axioms step220
theorem h220 : NestedArithmetic.compile e220=p220 := StagedExprCompile.compile_times e220 e217 e219 p217 p219 p220 rfl h217 h219 step220
#print axioms h220
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
