/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode033
import Proofs.RadenkovicGutmanD27Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2187],[0,2187,-1350]],[[0,0,0],[0,0,0],[0,0]],[[0,-19683,19683],[-19683,72171,-14823],[19683,-14823]],[[0,0,0],[0,0,0],[0,0]],[[-185895,216513,28431],[216513,56862,-53136],[28431,-53136]],[[0,0,0],[0,0,0],[0,0]],[[25515,1076004,-202662],[1076004,-1003833,-54297],[-202662,-54297]],[[0,0,0],[0,0,0],[0,0]],[[6819066,-1969029,-760347],[-1969029,-3375270,-20871],[-760347,-20871]],[[0,0,0],[0,0,0],[0,0]],[[20619927,-22311774,-1156356],[-22311774,-4949100,-2700],[-1156356,-2700]],[[0,0,0],[0,0],[0]],[[-33543909,-65966481,-963549],[-65966481,-4036446],[-963549]],[[0,0,0],[0,0],[0]],[[-362977470,-109558494,-471474],[-109558494,-1944945],[-471474]],[[0,0,0],[0,0],[0]],[[-1137902040,-118198359,-134865],[-118198359,-549666],[-134865]],[[0,0,0],[0,0],[0]],[[-2151229725,-87477597,-20871],[-87477597,-84213],[-20871]],[[0,0,0],[0,0],[0]],[[-2816599500,-45323550,-1350],[-45323550,-5400],[-1350]],[[0,0],[0]],[[-2697732324,-16430850],[-16430850]],[[0,0],[0]],[[-1939921272,-4083912],[-4083912]],[[0,0],[0]],[[-1059374835,-663066],[-663066]],[[0,0],[0]],[[-440051373,-63342],[-63342]],[[0,0],[0]],[[-138055266,-2700],[-2700]],[[0]],[[-32153436]],[[0]],[[-5386311]],[[0]],[[-613251]],[[0]],[[-42471]],[[0]],[[-1350]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
