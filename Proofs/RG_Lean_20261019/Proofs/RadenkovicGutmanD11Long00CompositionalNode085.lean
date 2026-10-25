/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode073
import Proofs.RadenkovicGutmanD11Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-792,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7128,-33264,0],[-33264,-11418,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-620730,-461538,0],[-461538,-62788,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-8943858,-2747052,0],[-2747052,-174394,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-61624992,-9267830,0],[-9267830,-270820,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-256483018,-19790716,0],[-19790716,-246664,0],[0,0]],[[0,0,0],[0,0],[0]],[[-715409398,-28347990,0],[-28347990,-133628],[0]],[[0,0,0],[0,0],[0]],[[-1417117724,-28156392,0],[-28156392,-42218],[0]],[[0,0,0],[0,0],[0]],[[-2066177696,-19738444,0],[-19738444,-7172],[0]],[[0,0,0],[0,0],[0]],[[-2268940102,-9819128,0],[-9819128,-506],[0]],[[0,0,0],[0,0],[0]],[[-1903855228,-3441438,0],[-3441438,0],[0]],[[0,0],[0]],[[-1230364300,-830060],[-830060]],[[0,0],[0]],[[-613749928,-131054],[-131054]],[[0,0],[0]],[[-235499990,-12188],[-12188]],[[0,0],[0]],[[-68803966,-506],[-506]],[[0,0],[0]],[[-15015660,0],[0]],[[0]],[[-2368520]],[[0]],[[-254914]],[[0]],[[-16742]],[[0]],[[-506]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
