/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode043
import Proofs.RadenkovicGutmanD12Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-1296],[0,-2592,720],[-1296,720]],[[0,0,0],[0,0,0],[0,0]],[[0,-51840,-4752],[-51840,1296,3120],[-4752,3120]],[[0,0,0],[0,0,0],[0,0]],[[-486000,-440640,7200],[-440640,86400,3840],[7200,3840]],[[0,0,0],[0,0,0],[0,0]],[[-5994000,-1470096,59328],[-1470096,305616,1680],[59328,1680]],[[0,0,0],[0,0,0],[0,0]],[[-32879520,-2237520,117744],[-2237520,488928,240],[117744,240]],[[0,0,0],[0,0],[0]],[[-106026480,-545328,116640],[-545328,432000],[116640]],[[0,0,0],[0,0],[0]],[[-222859824,3896544,64896],[3896544,222912],[64896]],[[0,0,0],[0,0],[0]],[[-317798112,7681248,20544],[7681248,66768],[20544]],[[0,0,0],[0,0],[0]],[[-305287200,7696608,3456],[7696608,10752],[3456]],[[0,0,0],[0,0],[0]],[[-179071440,4865184,240],[4865184,720],[240]],[[0,0],[0]],[[-29484864,2042112],[2042112]],[[0,0],[0]],[[54355680,569520],[569520]],[[0,0],[0]],[[62123616,101616],[101616]],[[0,0],[0]],[[36843120,10512],[10512]],[[0,0],[0]],[[14479056,480],[480]],[[0]],[[3958560]],[[0]],[[749280]],[[0]],[[94032]],[[0]],[[7056]],[[0]],[[240]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
