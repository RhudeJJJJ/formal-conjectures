/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode035
import Proofs.RadenkovicGutmanD28Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-2352],[0,-2352]],[[0,0,0],[0,0,0],[0,0]],[[0,-21168,-21168],[-21168,-84672,-10192],[-21168,-10192]],[[0,0,0],[0,0,0],[0,0]],[[-381024,-846720,-148176],[-846720,-592704,-12544],[-148176,-12544]],[[0,0,0],[0,0,0],[0,0]],[[-9398592,-7056000,-409248],[-7056000,-1636992,-5488],[-409248,-5488]],[[0,0,0],[0,0,0],[0,0]],[[-83994624,-27921376,-593488],[-27921376,-2373952,-784],[-593488,-784]],[[0,0,0],[0,0],[0]],[[-407921472,-65249184,-498624],[-65249184,-1994496],[-498624]],[[0,0,0],[0,0],[0]],[[-1261579872,-99197952,-250096],[-99197952,-1000384],[-250096]],[[0,0,0],[0,0],[0]],[[-2696132096,-103119520,-73696],[-103119520,-294784],[-73696]],[[0,0,0],[0,0],[0]],[[-4175941504,-75167568,-11760],[-75167568,-47040],[-11760]],[[0,0,0],[0,0],[0]],[[-4827255776,-38758608,-784],[-38758608,-3136],[-784]],[[0,0],[0]],[[-4240212256,-14056336],[-14056336]],[[0,0],[0]],[[-2858474976,-3504480],[-3504480]],[[0,0],[0]],[[-1483955200,-571536],[-571536]],[[0,0],[0]],[[-591600128,-54880],[-54880]],[[0,0],[0]],[[-179355680,-2352],[-2352]],[[0]],[[-40576704]],[[0]],[[-6629504]],[[0]],[[-738528]],[[0]],[[-50176]],[[0]],[[-1568]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
