/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode289
import Proofs.RadenkovicGutmanD19Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e290 : NestedArithmetic.Expr 3 := .times e289 e003
noncomputable def p290 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[1444,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[43320,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[596372,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[4993352,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[28415032,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[116337304,1444,0],[1444,0],[0]],[[0,0,0],[0,0],[0]],[[353899852,31768,0],[31768,0],[0]],[[0,0,0],[0,0],[0]],[[814592168,310460,0],[310460,0],[0]],[[0,0,0],[0,0],[0]],[[1431468968,1776120,0],[1776120,0],[0]],[[0,0,0],[0,0],[0]],[[1923815208,6600524,0],[6600524,0],[0]],[[0,0,0],[0,0],[0]],[[1967725804,16721520,361],[16721520,722],[361]],[[0,0,0],[0,0],[0]],[[1513228248,29495144,5054],[29495144,10108],[5054]],[[0,0,0],[0,0],[0]],[[856254456,36359920,29241],[36359920,58482],[29241]],[[0,0,0],[0,0],[0]],[[343952136,30975244,90250],[30975244,180500],[90250]],[[0,0,0],[0,0],[0]],[[92284596,17717880,160284],[17717880,320568],[160284]],[[0,0,0],[0,0],[0]],[[14737464,6433020,165338],[6433020,330676],[165338]],[[0,0,0],[0,0],[0]],[[1052676,1325592,95665],[1325592,191330],[95665]],[[0,0,0],[0,0],[0]],[[0,116964,28158],[116964,56316],[28158]],[[0,0,0],[0,0],[0]],[[0,0,3249],[0,6498],[3249]]]
theorem step290 : p290=NestedArithmetic.mul p289 p003 := by decide +kernel
#print axioms step290
theorem h290 : NestedArithmetic.compile e290=p290 := StagedExprCompile.compile_times e290 e289 e003 p289 p003 p290 rfl h289 h003 step290
#print axioms h290
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
