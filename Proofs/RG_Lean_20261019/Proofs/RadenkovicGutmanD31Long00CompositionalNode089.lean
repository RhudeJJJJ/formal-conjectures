/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode033
import Proofs.RadenkovicGutmanD31Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2883],[0,2883,-1798]],[[0,0,0],[0,0,0],[0,0]],[[0,-25947,25947],[-25947,95139,-19871],[25947,-19871]],[[0,0,0],[0,0,0],[0,0]],[[-243567,285417,35991],[285417,69006,-70928],[35991,-70928]],[[0,0,0],[0,0,0],[0,0]],[[59427,1391652,-275094],[1391652,-1355041,-72385],[-275094,-72385]],[[0,0,0],[0,0,0],[0,0]],[[9068058,-2809933,-1020179],[-2809933,-4520854,-27807],[-1020179,-27807]],[[0,0,0],[0,0,0],[0,0]],[[26807343,-30180174,-1546404],[-30180174,-6612300,-3596],[-1546404,-3596]],[[0,0,0],[0,0],[0]],[[-47790685,-88586809,-1286469],[-88586809,-5386126],[-1286469]],[[0,0,0],[0,0],[0]],[[-491677422,-146691566,-628866],[-146691566,-2593305],[-628866]],[[0,0,0],[0,0],[0]],[[-1530152312,-157999343,-179769],[-157999343,-732530],[-179769]],[[0,0,0],[0,0],[0]],[[-2883811301,-116809829,-27807],[-116809829,-112189],[-27807]],[[0,0,0],[0,0],[0]],[[-3769072876,-60475854,-1798],[-60475854,-7192],[-1798]],[[0,0],[0]],[[-3605798852,-21911730],[-21911730]],[[0,0],[0]],[[-2590745144,-5443848],[-5443848]],[[0,0],[0]],[[-1413895275,-883562],[-883562]],[[0,0],[0]],[[-587025765,-84382],[-84382]],[[0,0],[0]],[[-184091826,-3596],[-3596]],[[0]],[[-42861468]],[[0]],[[-7178143]],[[0]],[[-817067]],[[0]],[[-56575]],[[0]],[[-1798]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
