/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode033
import Proofs.RadenkovicGutmanD32Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3072],[0,3072,-1920]],[[0,0,0],[0,0,0],[0,0]],[[0,-27648,27648],[-27648,101376,-21248],[27648,-21248]],[[0,0,0],[0,0,0],[0,0]],[[-259200,304128,38016],[304128,72192,-75776],[38016,-75776]],[[0,0,0],[0,0,0],[0,0]],[[69120,1476864,-294912],[1476864,-1451008,-77312],[-294912,-77312]],[[0,0,0],[0,0,0],[0,0]],[[9680256,-3042304,-1091072],[-3042304,-4833280,-29696],[-1091072,-29696]],[[0,0,0],[0,0,0],[0,0]],[[28480512,-32331264,-1652736],[-32331264,-7065600,-3840],[-1652736,-3840]],[[0,0,0],[0,0],[0]],[[-51726464,-94759936,-1374464],[-94759936,-5753856],[-1374464]],[[0,0,0],[0,0],[0]],[[-526873600,-156817664,-671744],[-156817664,-2769920],[-671744]],[[0,0,0],[0,0],[0]],[[-1637233920,-168848384,-192000],[-168848384,-782336],[-192000]],[[0,0,0],[0,0],[0]],[[-3083645440,-124803072,-29696],[-124803072,-119808],[-29696]],[[0,0,0],[0,0],[0]],[[-4028771840,-64604160,-1920],[-64604160,-7680],[-1920]],[[0,0],[0]],[[-3853315584,-23404800],[-23404800]],[[0,0],[0]],[[-2768105472,-5814272],[-5814272]],[[0,0],[0]],[[-1510492160,-943616],[-943616]],[[0,0],[0]],[[-627067008,-90112],[-90112]],[[0,0],[0]],[[-196632576,-3840],[-3840]],[[0]],[[-45778176]],[[0]],[[-7666176]],[[0]],[[-872576]],[[0]],[[-60416]],[[0]],[[-1920]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
