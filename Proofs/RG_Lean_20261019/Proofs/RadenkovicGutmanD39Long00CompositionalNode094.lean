/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode035
import Proofs.RadenkovicGutmanD39Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-13689],[0,-27378,8658],[-13689,8658]],[[0,0,0],[0,0,0],[0,0]],[[0,-373815,-40716],[-373815,74412,37518],[-40716,37518]],[[0,0,0],[0,0,0],[0,0]],[[-2293434,-1934361,142389],[-1934361,1375686,46176],[142389,46176]],[[0,0,0],[0,0,0],[0,0]],[[-15915042,1840293,809874],[1840293,4632732,20202],[809874,20202]],[[0,0,0],[0,0,0],[0,0]],[[1274130,37455054,1509378],[37455054,7388160,2886],[1509378,2886]],[[0,0,0],[0,0],[0]],[[386995752,128057553,1455246],[128057553,6581484],[1455246]],[[0,0,0],[0,0],[0]],[[1953995472,235970631,797433],[235970631,3436134],[797433]],[[0,0,0],[0,0],[0]],[[5322069948,276721224,249990],[276721224,1042548],[249990]],[[0,0,0],[0,0],[0]],[[9582608490,219421683,41769],[219421683,170118],[41769]],[[0,0,0],[0,0],[0]],[[12297225486,120454893,2886],[120454893,11544],[2886]],[[0,0],[0]],[[11672806236,45862908],[45862908]],[[0,0],[0]],[[8357438466,11888955],[11888955]],[[0,0],[0]],[[4553339622,2001987],[2001987]],[[0,0],[0]],[[1888719924,197457],[197457]],[[0,0],[0]],[[591949488,8658],[8658]],[[0]],[[137759544]],[[0]],[[23062494]],[[0]],[[2624310]],[[0]],[[181662]],[[0]],[[5772]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
