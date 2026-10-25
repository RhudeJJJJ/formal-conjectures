/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode035
import Proofs.RadenkovicGutmanD32Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-3072],[0,-3072]],[[0,0,0],[0,0,0],[0,0]],[[0,-27648,-46080],[-27648,-147456,-13504],[-46080,-13504]],[[0,0,0],[0,0,0],[0,0]],[[-497664,-1715904,-355008],[-1715904,-1100544,-17216],[-355008,-17216]],[[0,0,0],[0,0,0],[0,0]],[[-17283456,-16086528,-1089344],[-16086528,-3271936,-8192],[-1089344,-8192]],[[0,0,0],[0,0,0],[0,0]],[[-178488576,-69540352,-1746560],[-69540352,-5110272,-1472],[-1746560,-1472]],[[0,0,0],[0,0,0],[0,0]],[[-954261504,-175464320,-1609024],[-175464320,-4617472,-64],[-1609024,-64]],[[0,0,0],[0,0],[0]],[[-3181884672,-285875840,-879360],[-285875840,-2493440],[-879360]],[[0,0,0],[0,0],[0]],[[-7246549376,-316735488,-282560],[-316735488,-798464],[-282560]],[[0,0,0],[0,0],[0]],[[-11871868928,-245114496,-50048],[-245114496,-142848],[-50048]],[[0,0,0],[0,0],[0]],[[-14441399808,-133885248,-4032],[-133885248,-12032],[-4032]],[[0,0,0],[0,0],[0]],[[-13300916096,-51442496,-64],[-51442496,-256],[-64]],[[0,0],[0]],[[-9379325056,-13642304],[-13642304]],[[0,0],[0]],[[-5086650240,-2394496],[-2394496]],[[0,0],[0]],[[-2118172672,-255552],[-255552]],[[0,0],[0]],[[-671731712,-13696],[-13696]],[[0,0],[0]],[[-159578240,-192],[-192]],[[0]],[[-27601664]],[[0]],[[-3312128]],[[0]],[[-252800]],[[0]],[[-10240]],[[0]],[[-128]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
