/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode289
import Proofs.RadenkovicGutmanD13Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e290 : NestedArithmetic.Expr 3 := .times e289 e003
noncomputable def p290 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[676,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[20280,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[279188,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[2337608,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[13302328,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[54462616,676,0],[676,0],[0]],[[0,0,0],[0,0],[0]],[[165676108,14872,0],[14872,0],[0]],[[0,0,0],[0,0],[0]],[[381346472,145340,0],[145340,0],[0]],[[0,0,0],[0,0],[0]],[[670133672,831480,0],[831480,0],[0]],[[0,0,0],[0,0],[0]],[[900622632,3089996,0],[3089996,0],[0]],[[0,0,0],[0,0],[0]],[[921179116,7828080,169],[7828080,338],[169]],[[0,0,0],[0,0],[0]],[[708408792,13807976,2366],[13807976,4732],[2366]],[[0,0,0],[0,0],[0]],[[400850424,17021680,13689],[17021680,27378],[13689]],[[0,0,0],[0,0],[0]],[[161019144,14500876,42250],[14500876,84500],[42250]],[[0,0,0],[0,0],[0]],[[43202484,8294520,75036],[8294520,150072],[75036]],[[0,0,0],[0,0],[0]],[[6899256,3011580,77402],[3011580,154804],[77402]],[[0,0,0],[0,0],[0]],[[492804,620568,44785],[620568,89570],[44785]],[[0,0,0],[0,0],[0]],[[0,54756,13182],[54756,26364],[13182]],[[0,0,0],[0,0],[0]],[[0,0,1521],[0,3042],[1521]]]
theorem step290 : p290=NestedArithmetic.mul p289 p003 := by decide +kernel
#print axioms step290
theorem h290 : NestedArithmetic.compile e290=p290 := StagedExprCompile.compile_times e290 e289 e003 p289 p003 p290 rfl h289 h003 step290
#print axioms h290
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
