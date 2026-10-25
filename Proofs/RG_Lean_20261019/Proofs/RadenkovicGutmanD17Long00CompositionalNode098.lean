/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode097
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e098 : NestedArithmetic.Expr 3 := .scaled (-1) e097
noncomputable def p098 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,867],[0,867]],[[0,0,0],[0,0,0],[0,0]],[[0,-7803,13005],[-7803,39015,3859],[13005,3859]],[[0,0,0],[0,0,0],[0,0]],[[-117045,258417,100623],[258417,289476,5066],[100623,5066]],[[0,0,0],[0,0,0],[0,0]],[[677025,3160368,310454],[3160368,856239,2567],[310454,2567]],[[0,0,0],[0,0,0],[0,0]],[[19936206,14907725,501245],[14907725,1334160,527],[501245,527]],[[0,0,0],[0,0,0],[0,0]],[[139032579,39407972,466174],[39407972,1207544,34],[466174,34]],[[0,0,0],[0,0],[0]],[[528153739,66269077,258315],[66269077,656914],[258315]],[[0,0,0],[0,0],[0]],[[1303980784,75270050,84830],[75270050,213775],[84830]],[[0,0,0],[0,0],[0]],[[2261470152,59508789,15623],[59508789,39508],[15623]],[[0,0,0],[0,0],[0]],[[2873619191,33148759,1377],[33148759,3587],[1377]],[[0,0,0],[0,0],[0]],[[2741837078,12982390,34],[12982390,102],[34]],[[0,0],[0]],[[1991731356,3512370],[3512370]],[[0,0],[0]],[[1108247612,630938],[630938]],[[0,0],[0]],[[472067033,69496],[69496]],[[0,0],[0]],[[152787415,3944],[3944]],[[0,0],[0]],[[36982140,68],[68]],[[0]],[[6510660]],[[0]],[[795005]],[[0]],[[61829]],[[0]],[[2567]],[[0]],[[34]]]
theorem step098 : p098=NestedHorner.scale (-1) p097 := by decide +kernel
#print axioms step098
theorem h098 : NestedArithmetic.compile e098=p098 := StagedExprCompile.compile_scaled (-1) e098 e097 p097 p098 rfl h097 step098
#print axioms h098
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
