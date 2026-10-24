/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e112 : NestedArithmetic.Expr 3 := .pow e032 2
noncomputable def p112 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,16]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-288,288],[0,288]],[[0,0,0],[0,0,0],[0,0]],[[1296,-2592,1296],[-2592,2688,768],[1296,768]],[[0,0,0],[0,0,0],[0,0]],[[-864,-6048,6912],[-6048,19168,704],[6912,704]],[[0,0,0],[0,0,0],[0,0]],[[-47952,44064,15552],[44064,47552,256],[15552,256]],[[0,0,0],[0,0,0],[0,0]],[[-132000,276096,19200],[276096,62592,32],[19200,32]],[[0,0,0],[0,0],[0]],[[277840,730528,14176],[730528,48704],[14176]],[[0,0,0],[0,0],[0]],[[2636224,1168480,6400],[1168480,23008],[6400]],[[0,0,0],[0,0],[0]],[[8236384,1249472,1728],[1249472,6464],[1728]],[[0,0,0],[0,0],[0]],[[15837024,929792,256],[929792,992],[256]],[[0,0,0],[0,0],[0]],[[21314944,488096,16],[488096,64],[16]],[[0,0],[0]],[[21136512,180000],[180000]],[[0,0],[0]],[[15815552,45600],[45600]],[[0,0],[0]],[[9018400,7552],[7552]],[[0,0],[0]],[[3920592,736],[736]],[[0,0],[0]],[[1289024,32],[32]],[[0]],[[314848]],[[0]],[[55328]],[[0]],[[6608]],[[0]],[[480]],[[0]],[[16]]]
theorem step112 : p112=NestedArithmetic.power p032 2 := by decide +kernel
#print axioms step112
theorem h112 : NestedArithmetic.compile e112=p112 := StagedExprCompile.compile_pow 2 e112 e032 p032 p112 rfl h032 step112
#print axioms h112
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
