/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode263
import Proofs.RadenkovicGutmanD2Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e264 : NestedArithmetic.Expr 3 := .times e263 e003
noncomputable def p264 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,0],[0,0],[0,0]],[[-8,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-248,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3528,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-30528,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-179568,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-760112,-12,0],[-12,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2391272,-268,0],[-268,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5693512,-2660,0],[-2660,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-10350912,-15464,0],[-15464,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-14391832,-58436,0],[-58436,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-15225624,-150636,-4],[-150636,-8,0],[-4,0]],[[0,0,0],[0,0,0],[0,0]],[[-12104464,-270544,-56],[-270544,-112,0],[-56,0]],[[0,0,0],[0,0,0],[0,0]],[[-7074384,-339748,-324],[-339748,-648,0],[-324,0]],[[0,0,0],[0,0,0],[0,0]],[[-2931264,-294892,-1000],[-294892,-2000,0],[-1000,0]],[[0,0,0],[0,0,0],[0,0]],[[-809784,-171800,-1776],[-171800,-3552,0],[-1776,0]],[[0,0,0],[0,0,0],[0,0]],[[-132840,-63468,-1832],[-63468,-3664,0],[-1832,0]],[[0,0,0],[0,0,0],[0,0]],[[-9720,-13284,-1060],[-13284,-2120,0],[-1060,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-1188,-312],[-1188,-624,0],[-312,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,-36],[0,-72,0],[-36,0]]]
theorem step264 : p264=NestedArithmetic.mul p263 p003 := by decide +kernel
#print axioms step264
theorem h264 : NestedArithmetic.compile e264=p264 := StagedExprCompile.compile_times e264 e263 e003 p263 p003 p264 rfl h263 h003 step264
#print axioms h264
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
