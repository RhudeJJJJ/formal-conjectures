/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode073
import Proofs.RadenkovicGutmanD30Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-2160,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-19440,-213840,0],[-213840,-51660,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3724380,-3043980,0],[-3043980,-349080,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-57573180,-18490680,0],[-18490680,-1079820,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-409137120,-63386100,0],[-63386100,-1782840,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1735177740,-137039640,0],[-137039640,-1685040,0],[0,0]],[[0,0,0],[0,0],[0]],[[-4904010660,-198191460,0],[-198191460,-934440],[0]],[[0,0,0],[0,0],[0]],[[-9810591240,-198350640,0],[-198350640,-299820],[0]],[[0,0,0],[0,0],[0]],[[-14415574560,-139897560,0],[-139897560,-51480],[0]],[[0,0,0],[0,0],[0]],[[-15930319380,-69939840,0],[-69939840,-3660],[0]],[[0,0,0],[0,0],[0]],[[-13437117960,-24613860,0],[-24613860,0],[0]],[[0,0],[0]],[[-8722134600,-5957400],[-5957400]],[[0,0],[0]],[[-4367382480,-943380],[-943380]],[[0,0],[0]],[[-1681284660,-87960],[-87960]],[[0,0],[0]],[[-492613140,-3660],[-3660]],[[0,0],[0]],[[-107778600,0],[0]],[[0]],[[-17038800]],[[0]],[[-1837500]],[[0]],[[-120900]],[[0]],[[-3660]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
