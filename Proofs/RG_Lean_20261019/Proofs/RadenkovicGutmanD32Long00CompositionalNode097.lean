/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode051
import Proofs.RadenkovicGutmanD32Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-3072],[0,-3072]],[[0,0,0],[0,0,0],[0,0]],[[0,27648,-46080],[27648,-138240,-13504],[-46080,-13504]],[[0,0,0],[0,0,0],[0,0]],[[414720,-914112,-355008],[-914112,-1020096,-17216],[-355008,-17216]],[[0,0,0],[0,0,0],[0,0]],[[-2376000,-11141568,-1089344],[-11141568,-2995584,-8192],[-1089344,-8192]],[[0,0,0],[0,0,0],[0,0]],[[-70082496,-52365440,-1746560],[-52365440,-4624320,-1472],[-1746560,-1472]],[[0,0,0],[0,0,0],[0,0]],[[-487766784,-137872832,-1609024],[-137872832,-4133504,-64],[-1609024,-64]],[[0,0,0],[0,0],[0]],[[-1848409024,-230801152,-879360],[-230801152,-2209024],[-879360]],[[0,0,0],[0,0],[0]],[[-4551365824,-260767040,-282560],[-260767040,-699520],[-282560]],[[0,0,0],[0,0],[0]],[[-7870119552,-204849024,-50048],[-204849024,-123328],[-50048]],[[0,0,0],[0,0],[0]],[[-9967767296,-113193664,-4032],[-113193664,-10112],[-4032]],[[0,0,0],[0,0],[0]],[[-9475448768,-43862080,-64],[-43862080,-192],[-64]],[[0,0],[0]],[[-6853637376,-11690880],[-11690880]],[[0,0],[0]],[[-3794043392,-2052608],[-2052608]],[[0,0],[0]],[[-1605966848,-217216],[-217216]],[[0,0],[0]],[[-515632960,-11264],[-11264]],[[0,0],[0]],[[-123483840,-128],[-128]],[[0]],[[-21413760]],[[0]],[[-2554880]],[[0]],[[-190784]],[[0]],[[-7232]],[[0]],[[-64]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
