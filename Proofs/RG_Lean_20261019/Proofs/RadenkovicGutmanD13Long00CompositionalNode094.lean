/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode035
import Proofs.RadenkovicGutmanD13Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-1521],[0,-3042,858],[-1521,858]],[[0,0,0],[0,0,0],[0,0]],[[0,-42471,-5460],[-42471,4524,3718],[-5460,3718]],[[0,0,0],[0,0,0],[0,0]],[[-271674,-252369,9269],[-252369,126646,4576],[9269,4576]],[[0,0,0],[0,0,0],[0,0]],[[-2183922,-107523,71890],[-107523,442364,2002],[71890,2002]],[[0,0,0],[0,0,0],[0,0]],[[-3572478,2927054,141466],[2927054,715936,286],[141466,286]],[[0,0,0],[0,0],[0]],[[24962184,11343449,139646],[11343449,643084],[139646]],[[0,0,0],[0,0],[0]],[[161326464,21832655,77545],[21832655,337558],[77545]],[[0,0,0],[0,0],[0]],[[472124380,26187096,24518],[26187096,102804],[24518]],[[0,0,0],[0,0],[0]],[[880083802,21056451,4121],[21056451,16822],[4121]],[[0,0,0],[0,0],[0]],[[1152908302,11670061,286],[11670061,1144],[286]],[[0,0],[0]],[[1109486092,4474340],[4474340]],[[0,0],[0]],[[802209122,1166035],[1166035]],[[0,0],[0]],[[440309558,197171],[197171]],[[0,0],[0]],[[183698580,19513],[19513]],[[0,0],[0]],[[57841472,858],[858]],[[0]],[[13512408]],[[0]],[[2269358]],[[0]],[[258934]],[[0]],[[17966]],[[0]],[[572]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
