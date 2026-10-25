/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,529]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-9522,9522],[0,9522]],[[0,0,0],[0,0,0],[0,0]],[[42849,-85698,42849],[-85698,88872,25392],[42849,25392]],[[0,0,0],[0,0,0],[0,0]],[[-28566,-199962,228528],[-199962,633742,23276],[228528,23276]],[[0,0,0],[0,0,0],[0,0]],[[-1585413,1456866,514188],[1456866,1572188,8464],[514188,8464]],[[0,0,0],[0,0,0],[0,0]],[[-4364250,9128424,634800],[9128424,2069448,1058],[634800,1058]],[[0,0,0],[0,0],[0]],[[9186085,24153082,468694],[24153082,1610276],[468694]],[[0,0,0],[0,0],[0]],[[87160156,38632870,211600],[38632870,760702],[211600]],[[0,0,0],[0,0],[0]],[[272315446,41310668,57132],[41310668,213716],[57132]],[[0,0,0],[0,0],[0]],[[523611606,30741248,8464],[30741248,32798],[8464]],[[0,0,0],[0,0],[0]],[[704725336,16137674,529],[16137674,2116],[529]],[[0,0],[0]],[[698825928,5951250],[5951250]],[[0,0],[0]],[[522901688,1507650],[1507650]],[[0,0],[0]],[[298170850,249688],[249688]],[[0,0],[0]],[[129624573,24334],[24334]],[[0,0],[0]],[[42618356,1058],[1058]],[[0]],[[10409662]],[[0]],[[1829282]],[[0]],[[218477]],[[0]],[[15870]],[[0]],[[529]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
