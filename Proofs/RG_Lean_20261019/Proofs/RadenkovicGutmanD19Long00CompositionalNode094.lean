/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode035
import Proofs.RadenkovicGutmanD19Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-3249],[0,-6498,1938],[-3249,1938]],[[0,0,0],[0,0,0],[0,0]],[[0,-89775,-10716],[-89775,13452,8398],[-10716,8398]],[[0,0,0],[0,0,0],[0,0]],[[-563274,-501201,26429],[-501201,297046,10336],[26429,10336]],[[0,0,0],[0,0,0],[0,0]],[[-4244562,86013,171874],[86013,1018172,4522],[171874,4522]],[[0,0,0],[0,0,0],[0,0]],[[-3873150,7501694,328738],[7501694,1635520,646],[328738,646]],[[0,0,0],[0,0],[0]],[[71572392,27149993,320606],[27149993,1462924],[320606]],[[0,0,0],[0,0],[0]],[[401052912,51074831,176833],[51074831,765814],[176833]],[[0,0,0],[0,0],[0]],[[1129129948,60551784,55670],[60551784,232788],[55670]],[[0,0,0],[0,0],[0]],[[2066778010,48341643,9329],[48341643,38038],[9329]],[[0,0,0],[0,0],[0]],[[2678697406,26662453,646],[26662453,2584],[646]],[[0,0],[0]],[[2559678556,10186508],[10186508]],[[0,0],[0]],[[1841485586,2647555],[2647555]],[[0,0],[0]],[[1006936502,446747],[446747]],[[0,0],[0]],[[418866324,44137],[44137]],[[0,0],[0]],[[131579408,1938],[1938]],[[0]],[[30679224]],[[0]],[[5144174]],[[0]],[[586150]],[[0]],[[40622]],[[0]],[[1292]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
