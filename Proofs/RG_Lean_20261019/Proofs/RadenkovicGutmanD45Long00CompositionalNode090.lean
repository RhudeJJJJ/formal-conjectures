/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode035
import Proofs.RadenkovicGutmanD45Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-6075],[0,-6075]],[[0,0,0],[0,0,0],[0,0]],[[0,-54675,-91125],[-54675,-291600,-26595],[-91125,-26595]],[[0,0,0],[0,0,0],[0,0]],[[-984150,-3392280,-701055],[-3392280,-2172420,-33570],[-701055,-33570]],[[0,0,0],[0,0,0],[0,0]],[[-34160940,-31772250,-2147310],[-31772250,-6442740,-15615],[-2147310,-15615]],[[0,0,0],[0,0,0],[0,0]],[[-352529820,-137189700,-3434805],[-137189700,-10029420,-2655],[-3434805,-2655]],[[0,0,0],[0,0,0],[0,0]],[[-1883172240,-345685410,-3154230],[-345685410,-9020520,-90],[-3154230,-90]],[[0,0,0],[0,0],[0]],[[-6273277470,-562287690,-1715715],[-562287690,-4837860],[-1715715]],[[0,0,0],[0,0],[0]],[[-14271499620,-621730620,-547110],[-621730620,-1532340],[-547110]],[[0,0,0],[0,0],[0]],[[-23351348160,-479914425,-95535],[-479914425,-268740],[-95535]],[[0,0,0],[0,0],[0]],[[-28363683690,-261257805,-7425],[-261257805,-21600],[-7425]],[[0,0,0],[0,0],[0]],[[-26077958010,-99922005,-90],[-99922005,-360],[-90]],[[0,0],[0]],[[-18350235810,-26322660],[-26322660]],[[0,0],[0]],[[-9925742160,-4571775],[-4571775]],[[0,0],[0]],[[-4119563700,-478710],[-478710]],[[0,0],[0]],[[-1300785930,-24525],[-24525]],[[0,0],[0]],[[-307207800,-270],[-270]],[[0]],[[-52691040]],[[0]],[[-6240690]],[[0]],[[-465480]],[[0]],[[-17910]],[[0]],[[-180]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
