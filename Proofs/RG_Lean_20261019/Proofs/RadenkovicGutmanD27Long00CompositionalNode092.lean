/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode089
import Proofs.RadenkovicGutmanD27Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,4374],[0,4374,-1350]],[[0,0,0],[0,0,0],[0,0]],[[0,0,52488],[0,177147,-5184],[52488,-5184]],[[0,0,0],[0,0,0],[0,0]],[[168399,1438317,281394],[1438317,841266,-40770],[281394,-40770]],[[0,0,0],[0,0,0],[0,0]],[[12333951,12537342,574452],[12537342,1331883,-48330],[574452,-48330]],[[0,0,0],[0,0,0],[0,0]],[[133988742,47613663,487458],[47613663,280422,-19764],[487458,-19764]],[[0,0,0],[0,0,0],[0,0]],[[700876071,102904236,-4482],[102904236,-1636308,-2646],[-4482,-2646]],[[0,0,0],[0,0],[0]],[[2236074633,138254769,-332154],[138254769,-2239866],[-332154]],[[0,0,0],[0,0],[0]],[[4809520206,116997534,-267624],[116997534,-1365741],[-267624]],[[0,0,0],[0,0],[0]],[[7342864488,57411882,-98442],[57411882,-444798],[-98442]],[[0,0,0],[0,0],[0]],[[8174747853,8646156,-17874],[8646156,-75141],[-17874]],[[0,0,0],[0,0],[0]],[[6704461206,-8283789,-1296],[-8283789,-5184],[-1296]],[[0,0],[0]],[[4025174742,-6567426],[-6567426]],[[0,0],[0]],[[1712099808,-2341521],[-2341521]],[[0,0],[0]],[[464552577,-474984],[-474984]],[[0,0],[0]],[[44530749,-53001],[-53001]],[[0,0],[0]],[[-22519026,-2538],[-2538]],[[0]],[[-12066732]],[[0]],[[-2957013]],[[0]],[[-425331]],[[0]],[[-34641]],[[0]],[[-1242]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
