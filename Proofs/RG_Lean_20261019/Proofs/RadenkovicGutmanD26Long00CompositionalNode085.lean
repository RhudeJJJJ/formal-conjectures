/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode073
import Proofs.RadenkovicGutmanD26Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-1872,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-16848,-162864,0],[-162864,-41028,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2857140,-2312388,0],[-2312388,-270088,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-43842708,-14018472,0],[-14018472,-825604,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-310600992,-47981180,0],[-47981180,-1354600,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1314854788,-103611976,0],[-103611976,-1275664,0],[0,0]],[[0,0,0],[0,0],[0]],[[-3711368908,-149710860,0],[-149710860,-705848],[0]],[[0,0,0],[0,0],[0]],[[-7417678424,-149724432,0],[-149724432,-226148],[0]],[[0,0,0],[0,0],[0]],[[-10891433696,-105541384,0],[-105541384,-38792],[0]],[[0,0,0],[0,0],[0]],[[-12028734172,-52739648,0],[-52739648,-2756],[0]],[[0,0,0],[0,0],[0]],[[-10141190488,-18553548,0],[-18553548,0],[0]],[[0,0],[0]],[[-6580015000,-4489160],[-4489160]],[[0,0],[0]],[[-3293615728,-710684],[-710684]],[[0,0],[0]],[[-1267539260,-66248],[-66248]],[[0,0],[0]],[[-371288476,-2756],[-2756]],[[0,0],[0]],[[-81215160,0],[0]],[[0]],[[-12836720]],[[0]],[[-1384084]],[[0]],[[-91052]],[[0]],[[-2756]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
