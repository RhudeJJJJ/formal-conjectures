/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode033
import Proofs.RadenkovicGutmanD17Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,289]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,5202],[0,5202]],[[0,0,0],[0,0,0],[0,0]],[[-23409,0,23409],[0,93636,13872],[23409,13872]],[[0,0,0],[0,0,0],[0,0]],[[-405756,421362,124848],[421362,499392,12716],[124848,12716]],[[0,0,0],[0,0,0],[0,0]],[[-1240677,3370896,280908],[3370896,1123632,4624],[280908,4624]],[[0,0,0],[0,0,0],[0,0]],[[5895600,12079044,346800],[12079044,1387200,578],[346800,578]],[[0,0,0],[0,0],[0]],[[56188247,25593840,256054],[25593840,1024216],[256054]],[[0,0,0],[0,0],[0]],[[207416456,35659710,115600],[35659710,462400],[115600]],[[0,0,0],[0,0],[0]],[[473836886,34374816,31212],[34374816,124848],[31212]],[[0,0,0],[0,0],[0]],[[754582468,23487608,4624],[23487608,18496],[4624]],[[0,0,0],[0,0],[0]],[[882667268,11458272,289],[11458272,1156],[289]],[[0,0],[0]],[[779182148,3962190],[3962190]],[[0,0],[0]],[[526312928,947920],[947920]],[[0,0],[0]],[[273428680,149124],[149124]],[[0,0],[0]],[[109031319,13872],[13872]],[[0,0],[0]],[[33056976,578],[578]],[[0]],[[7478742]],[[0]],[[1221892]],[[0]],[[136119]],[[0]],[[9248]],[[0]],[[289]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
