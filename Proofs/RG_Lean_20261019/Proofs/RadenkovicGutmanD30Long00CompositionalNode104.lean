/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode092
import Proofs.RadenkovicGutmanD30Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2160,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-19440,-19440,0],[-19440,-18180,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-507060,-215460,0],[-215460,-58920,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4926420,-1014120,0],[-1014120,-94020,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-25974720,-2677500,0],[-2677500,-79080,0],[0,0]],[[0,0,0],[0,0],[0]],[[-86276580,-4412040,0],[-4412040,-33360],[0]],[[0,0,0],[0,0],[0]],[[-195003180,-4756140,0],[-4756140,-4440],[0]],[[0,0,0],[0,0],[0]],[[-313467480,-3391440,0],[-3391440,1500],[0]],[[0,0,0],[0,0],[0]],[[-367538880,-1553640,0],[-1553640,600],[0]],[[0,0,0],[0,0],[0]],[[-317965020,-402240,0],[-402240,60],[0]],[[0,0],[0]],[[-202609560,-20940],[-20940]],[[0,0],[0]],[[-93151320,22200],[22200]],[[0,0],[0]],[[-29029200,7620],[7620]],[[0,0],[0]],[[-4867740,1080],[1080]],[[0,0],[0]],[[313860,60],[60]],[[0]],[[430920]],[[0]],[[123120]],[[0]],[[19020]],[[0]],[[1620]],[[0]],[[60]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
