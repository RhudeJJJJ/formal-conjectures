/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode081
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e084 : NestedArithmetic.Expr 3 := .scaled (-1) e081
noncomputable def p084 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,48600,0],[48600,8100,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[801900,704700,0],[704700,70200,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[13097700,4341600,0],[4341600,238500,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[95158800,15043500,0],[15043500,412200,0],[0,0]],[[0,0,0],[0,0],[0]],[[408820500,32788800,0],[32788800,399600],[0]],[[0,0,0],[0,0],[0]],[[1165616100,47715300,0],[47715300,225000],[0]],[[0,0,0],[0,0],[0]],[[2346996600,47984400,0],[47984400,72900],[0]],[[0,0,0],[0,0],[0]],[[3466004400,33973200,0],[33973200,12600],[0]],[[0,0,0],[0,0],[0]],[[3845645100,17037000,0],[17037000,900],[0]],[[0,0],[0]],[[3254520600,6011100],[6011100]],[[0,0],[0]],[[2118393000,1458000],[1458000]],[[0,0],[0]],[[1063231200,231300],[231300]],[[0,0],[0]],[[410136300,21600],[21600]],[[0,0],[0]],[[120381300,900],[900]],[[0]],[[26379000]],[[0]],[[4176000]],[[0]],[[450900]],[[0]],[[29700]],[[0]],[[900]]]
theorem step084 : p084=NestedHorner.scale (-1) p081 := by decide +kernel
#print axioms step084
theorem h084 : NestedArithmetic.compile e084=p084 := StagedExprCompile.compile_scaled (-1) e084 e081 p081 p084 rfl h081 step084
#print axioms h084
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
