/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode073
import Proofs.RadenkovicGutmanD6Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-432,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3888,-11664,0],[-11664,-5148,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-231660,-157788,0],[-157788,-24888,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3132108,-919512,0],[-919512,-63324,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-20925792,-3049380,0],[-3049380,-92760,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-85390428,-6423096,0],[-6423096,-81264,0],[0,0]],[[0,0,0],[0,0],[0]],[[-234807828,-9100500,0],[-9100500,-42888],[0]],[[0,0,0],[0,0],[0]],[[-460040424,-8960112,0],[-8960112,-13308],[0]],[[0,0,0],[0,0],[0]],[[-664872096,-6236664,0],[-6236664,-2232],[0]],[[0,0,0],[0,0],[0]],[[-724851012,-3084288,0],[-3084288,-156],[0]],[[0,0,0],[0,0],[0]],[[-604530408,-1075668,0],[-1075668,0],[0]],[[0,0],[0]],[[-388655400,-258360],[-258360]],[[0,0],[0]],[[-193008528,-40644],[-40644]],[[0,0],[0]],[[-73769700,-3768],[-3768]],[[0,0],[0]],[[-21478596,-156],[-156]],[[0,0],[0]],[[-4673160,0],[0]],[[0]],[[-735120]],[[0]],[[-78924]],[[0]],[[-5172]],[[0]],[[-156]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
