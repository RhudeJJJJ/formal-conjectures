/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode095
import Proofs.RadenkovicGutmanD11Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-792,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7128,-7128,0],[-7128,-6864,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-187704,-80784,0],[-80784,-23320,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1853280,-392040,0],[-392040,-40304,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-9987384,-1079760,0],[-1079760,-39072,0],[0,0]],[[0,0,0],[0,0],[0]],[[-34131592,-1887688,0],[-1887688,-22000],[0]],[[0,0,0],[0,0],[0]],[[-80034064,-2215840,0],[-2215840,-7128],[0]],[[0,0,0],[0,0],[0]],[[-134946592,-1797488,0],[-1797488,-1232],[0]],[[0,0,0],[0,0],[0]],[[-168500904,-1019040,0],[-1019040,-88],[0]],[[0,0,0],[0,0],[0]],[[-158712400,-402248,0],[-402248,0],[0]],[[0,0],[0]],[[-113968272,-108240],[-108240]],[[0,0],[0]],[[-62647552,-18920],[-18920]],[[0,0],[0]],[[-26305928,-1936],[-1936]],[[0,0],[0]],[[-8361320,-88],[-88]],[[0,0],[0]],[[-1975248,0],[0]],[[0]],[[-335808]],[[0]],[[-38808]],[[0]],[[-2728]],[[0]],[[-88]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
