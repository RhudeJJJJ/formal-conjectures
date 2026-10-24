/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e111 : NestedArithmetic.Expr 3 := .pow e032 2
noncomputable def p111 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,4]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-72,72],[0,72]],[[0,0,0],[0,0,0],[0,0]],[[324,-648,324],[-648,672,192],[324,192]],[[0,0,0],[0,0,0],[0,0]],[[-216,-1512,1728],[-1512,4792,176],[1728,176]],[[0,0,0],[0,0,0],[0,0]],[[-11988,11016,3888],[11016,11888,64],[3888,64]],[[0,0,0],[0,0,0],[0,0]],[[-33000,69024,4800],[69024,15648,8],[4800,8]],[[0,0,0],[0,0],[0]],[[69460,182632,3544],[182632,12176],[3544]],[[0,0,0],[0,0],[0]],[[659056,292120,1600],[292120,5752],[1600]],[[0,0,0],[0,0],[0]],[[2059096,312368,432],[312368,1616],[432]],[[0,0,0],[0,0],[0]],[[3959256,232448,64],[232448,248],[64]],[[0,0,0],[0,0],[0]],[[5328736,122024,4],[122024,16],[4]],[[0,0],[0]],[[5284128,45000],[45000]],[[0,0],[0]],[[3953888,11400],[11400]],[[0,0],[0]],[[2254600,1888],[1888]],[[0,0],[0]],[[980148,184],[184]],[[0,0],[0]],[[322256,8],[8]],[[0]],[[78712]],[[0]],[[13832]],[[0]],[[1652]],[[0]],[[120]],[[0]],[[4]]]
theorem step111 : p111=NestedArithmetic.power p032 2 := by decide +kernel
#print axioms step111
theorem h111 : NestedArithmetic.compile e111=p111 := StagedExprCompile.compile_pow 2 e111 e032 p032 p111 rfl h032 step111
#print axioms h111
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
