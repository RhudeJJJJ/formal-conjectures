/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode092
import Proofs.RadenkovicGutmanD41Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2952,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-26568,-26568,0],[-26568,-24846,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-692982,-294462,0],[-294462,-80524,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6732774,-1385964,0],[-1385964,-128494,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-35498784,-3659250,0],[-3659250,-108076,0],[0,0]],[[0,0,0],[0,0],[0]],[[-117911326,-6029788,0],[-6029788,-45592],[0]],[[0,0,0],[0,0],[0]],[[-266504346,-6500058,0],[-6500058,-6068],[0]],[[0,0,0],[0,0],[0]],[[-428405556,-4634968,0],[-4634968,2050],[0]],[[0,0,0],[0,0],[0]],[[-502303136,-2123308,0],[-2123308,820],[0]],[[0,0,0],[0,0],[0]],[[-434552194,-549728,0],[-549728,82],[0]],[[0,0],[0]],[[-276899732,-28618],[-28618]],[[0,0],[0]],[[-127306804,30340],[30340]],[[0,0],[0]],[[-39673240,10414],[10414]],[[0,0],[0]],[[-6652578,1476],[1476]],[[0,0],[0]],[[428942,82],[82]],[[0]],[[588924]],[[0]],[[168264]],[[0]],[[25994]],[[0]],[[2214]],[[0]],[[82]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
