/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode043
import Proofs.RadenkovicGutmanD27Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2187],[0,2187,-1350]],[[0,0,0],[0,0,0],[0,0]],[[0,19683,19683],[19683,80676,-14823],[19683,-14823]],[[0,0,0],[0,0,0],[0,0]],[[481140,804816,28431],[804816,130572,-53136],[28431,-53136]],[[0,0,0],[0,0,0],[0,0]],[[11095380,4790988,-202662],[4790988,-753408,-54297],[-202662,-54297]],[[0,0,0],[0,0,0],[0,0]],[[88446654,11178486,-760347],[11178486,-2942460,-20871],[-760347,-20871]],[[0,0,0],[0,0,0],[0,0]],[[376279020,6897474,-1156356],[6897474,-4529520,-2700],[-1156356,-2700]],[[0,0,0],[0,0],[0]],[[994382676,-22683672,-963549],[-22683672,-3800196],[-963549]],[[0,0,0],[0,0],[0]],[[1734537024,-65252250,-471474],[-65252250,-1868400],[-471474]],[[0,0,0],[0,0],[0]],[[2000794068,-86268051,-134865],[-86268051,-536436],[-134865]],[[0,0,0],[0,0],[0]],[[1377335934,-71176347,-20871],[-71176347,-83268],[-20871]],[[0,0,0],[0,0],[0]],[[209128986,-39467223,-1350],[-39467223,-5400],[-1350]],[[0,0],[0]],[[-702093690,-14984190],[-14984190]],[[0,0],[0]],[[-924932736,-3850119],[-3850119]],[[0,0],[0]],[[-662595336,-640818],[-640818]],[[0,0],[0]],[[-322019280,-62397],[-62397]],[[0,0],[0]],[[-111839940,-2700],[-2700]],[[0]],[[-27946620]],[[0]],[[-4925826]],[[0]],[[-582498]],[[0]],[[-41526]],[[0]],[[-1350]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
