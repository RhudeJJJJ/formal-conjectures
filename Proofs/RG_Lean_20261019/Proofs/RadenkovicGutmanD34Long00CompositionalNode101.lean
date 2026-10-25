/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode051
import Proofs.RadenkovicGutmanD34Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1156]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,27744],[0,27744,68]],[[0,0,0],[0,0,0],[0,0]],[[-93636,62424,156060],[62424,625464,86768],[156060,86768]],[[0,0,0],[0,0,0],[0,0]],[[-493884,4193424,941868],[4193424,3778080,91120],[941868,91120]],[[0,0,0],[0,0,0],[0,0]],[[22948164,34515576,2359872],[34515576,9475528,37672],[2359872,37672]],[[0,0,0],[0,0,0],[0,0]],[[273853068,132054776,3203480],[132054776,12876208,5712],[3203480,5712]],[[0,0,0],[0,0,0],[0,0]],[[1444527332,299304720,2576248],[299304720,10365376,136],[2576248,136]],[[0,0,0],[0,0],[0]],[[4616008708,444110992,1260176],[444110992,5074704],[1260176]],[[0,0,0],[0,0],[0]],[[10018678952,453411624,369376],[453411624,1488520],[369376]],[[0,0,0],[0,0],[0]],[[15653141000,326484184,60520],[326484184,243984],[60520]],[[0,0,0],[0,0],[0]],[[18204107144,167232808,4556],[167232808,18360],[4556]],[[0,0,0],[0,0],[0]],[[16073997216,60618328,68],[60618328,272],[68]],[[0,0],[0]],[[10894305840,15225880],[15225880]],[[0,0],[0]],[[5690525600,2534224],[2534224]],[[0,0],[0]],[[2285732756,255408],[255408]],[[0,0],[0]],[[699720612,12648],[12648]],[[0,0],[0]],[[160405608,136],[136]],[[0]],[[26716520]],[[0]],[[3069860]],[[0]],[[221204]],[[0]],[[8092]],[[0]],[[68]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
