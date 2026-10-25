/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode073
import Proofs.RadenkovicGutmanD22Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-1584,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-14256,-118800,0],[-118800,-31548,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2103948,-1681020,0],[-1681020,-201080,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-31975020,-10163736,0],[-10163736,-605308,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-225598560,-34715780,0],[-34715780,-984984,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-952675196,-74847608,0],[-74847608,-923120,0],[0,0]],[[0,0,0],[0,0],[0]],[[-2684503668,-108016436,0],[-108016436,-509256],[0]],[[0,0,0],[0,0],[0]],[[-5358560680,-107922672,0],[-107922672,-162844],[0]],[[0,0,0],[0,0],[0]],[[-7860235680,-76016952,0],[-76016952,-27896],[0]],[[0,0,0],[0,0],[0]],[[-8674085156,-37962496,0],[-37962496,-1980],[0]],[[0,0,0],[0,0],[0]],[[-7308128168,-13348148,0],[-13348148,0],[0]],[[0,0],[0]],[[-4739177960,-3228280],[-3228280]],[[0,0],[0]],[[-2371064080,-510884],[-510884]],[[0,0],[0]],[[-912124356,-47608],[-47608]],[[0,0],[0]],[[-267084708,-1980],[-1980]],[[0,0],[0]],[[-58403400,0],[0]],[[0]],[[-9228560]],[[0]],[[-994796]],[[0]],[[-65428]],[[0]],[[-1980]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
