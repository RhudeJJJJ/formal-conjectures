/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode097
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e098 : NestedArithmetic.Expr 3 := .scaled (-1) e097
noncomputable def p098 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1452],[0,1452]],[[0,0,0],[0,0,0],[0,0]],[[0,-13068,21780],[-13068,65340,6424],[21780,6424]],[[0,0,0],[0,0,0],[0,0]],[[-196020,432432,168168],[432432,483516,8316],[168168,8316]],[[0,0,0],[0,0,0],[0,0]],[[1128600,5279868,517484],[5279868,1425204,4092],[517484,4092]],[[0,0,0],[0,0,0],[0,0]],[[33260436,24861980,832700],[24861980,2210780,792],[832700,792]],[[0,0,0],[0,0,0],[0,0]],[[231729564,65594892,770924],[65594892,1989064,44],[770924,44]],[[0,0,0],[0,0],[0]],[[879255784,110065252,424380],[110065252,1072984],[424380]],[[0,0,0],[0,0],[0]],[[2168024364,124697980,137940],[124697980,344740],[137940]],[[0,0,0],[0,0],[0]],[[3754641352,98285484,24948],[98285484,62348],[24948]],[[0,0,0],[0,0],[0]],[[4763480876,54539144,2112],[54539144,5412],[2112]],[[0,0,0],[0,0],[0]],[[4536963508,21252220,44],[21252220,132],[44]],[[0,0],[0]],[[3288981696,5709440],[5709440]],[[0,0],[0]],[[1825603472,1014728],[1014728]],[[0,0],[0]],[[775307588,109736],[109736]],[[0,0],[0]],[[249982480,5984],[5984]],[[0,0],[0]],[[60204540,88],[88]],[[0]],[[10524360]],[[0]],[[1271380]],[[0]],[[97064]],[[0]],[[3872]],[[0]],[[44]]]
theorem step098 : p098=NestedHorner.scale (-1) p097 := by decide +kernel
#print axioms step098
theorem h098 : NestedArithmetic.compile e098=p098 := StagedExprCompile.compile_scaled (-1) e098 e097 p097 p098 rfl h097 step098
#print axioms h098
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
