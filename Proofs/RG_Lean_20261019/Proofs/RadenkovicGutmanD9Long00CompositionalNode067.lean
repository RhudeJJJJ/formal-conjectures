/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode043
import Proofs.RadenkovicGutmanD9Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,729],[0,1458,-756],[729,-756,196]],[[0,0,0],[0,0,0],[0,0]],[[0,26001,-486],[26001,-14454,252],[-486,252]],[[0,0,0],[0,0,0],[0,0]],[[190836,111699,-10287],[111699,-82986,5376],[-10287,5376]],[[0,0,0],[0,0,0],[0,0]],[[1435752,-51381,-9774],[-51381,-109582,6860],[-9774,6860]],[[0,0,0],[0,0,0],[0,0]],[[2570130,-1161144,35712],[-1161144,77332,2884],[35712,2884]],[[0,0,0],[0,0,0],[0,0]],[[-10970394,-2723349,95178],[-2723349,346428,392],[95178,392]],[[0,0,0],[0,0],[0]],[[-71736866,-2233393,99829],[-2233393,389694],[99829]],[[0,0,0],[0,0],[0]],[[-192971864,1427948,55846],[1427948,222250],[55846]],[[0,0,0],[0,0],[0]],[[-315666362,5294527,17469],[5294527,69910],[17469]],[[0,0,0],[0,0],[0]],[[-339596744,6007337,2884],[6007337,11550],[2884]],[[0,0,0],[0,0],[0]],[[-235805540,3971536,196],[3971536,784],[196]],[[0,0],[0]],[[-85423210,1694985],[1694985]],[[0,0],[0]],[[14403274,474413],[474413]],[[0,0],[0]],[[40257350,84371],[84371]],[[0,0],[0]],[[27537742,8666],[8666]],[[0,0],[0]],[[11421156,392],[392]],[[0]],[[3199530]],[[0]],[[612220]],[[0]],[[77108]],[[0]],[[5782]],[[0]],[[196]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
