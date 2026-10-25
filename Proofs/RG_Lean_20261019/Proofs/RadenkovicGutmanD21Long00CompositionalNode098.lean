/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode097
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e098 : NestedArithmetic.Expr 3 := .scaled (-1) e097
noncomputable def p098 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1323],[0,1323]],[[0,0,0],[0,0,0],[0,0]],[[0,-11907,19845],[-11907,59535,5859],[19845,5859]],[[0,0,0],[0,0,0],[0,0]],[[-178605,394065,153279],[394065,440748,7602],[153279,7602]],[[0,0,0],[0,0,0],[0,0]],[[1029105,4812696,471870],[4812696,1299879,3759],[471870,3759]],[[0,0,0],[0,0,0],[0,0]],[[30324294,22668597,759717],[22668597,2017848,735],[759717,735]],[[0,0,0],[0,0,0],[0,0]],[[211306347,59826732,703878],[59826732,1817256,42],[703878,42]],[[0,0,0],[0,0],[0]],[[801916731,100422189,387891],[100422189,981666],[387891]],[[0,0,0],[0,0],[0]],[[1977742200,113820042,126294],[113820042,316071],[126294]],[[0,0,0],[0,0],[0]],[[3425896824,89756541,22911],[89756541,57372],[22911]],[[0,0,0],[0,0],[0]],[[4347520191,49837767,1953],[49837767,5019],[1953]],[[0,0,0],[0,0],[0]],[[4141985358,19436382,42],[19436382,126],[42]],[[0,0],[0]],[[3003660828,5227698],[5227698]],[[0,0],[0]],[[1667899548,930762],[930762]],[[0,0],[0]],[[708681393,100968],[100968]],[[0,0],[0]],[[228643191,5544],[5544]],[[0,0],[0]],[[55111140,84],[84]],[[0]],[[9645300]],[[0]],[[1167285]],[[0]],[[89397]],[[0]],[[3591]],[[0]],[[42]]]
theorem step098 : p098=NestedHorner.scale (-1) p097 := by decide +kernel
#print axioms step098
theorem h098 : NestedArithmetic.compile e098=p098 := StagedExprCompile.compile_scaled (-1) e098 e097 p097 p098 rfl h097 step098
#print axioms h098
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
