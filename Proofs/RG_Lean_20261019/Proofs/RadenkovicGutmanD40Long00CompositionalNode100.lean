/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode043
import Proofs.RadenkovicGutmanD40Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-14400],[0,-28800,9120],[-14400,9120]],[[0,0,0],[0,0,0],[0,0]],[[0,-565920,-42720],[-565920,51360,39520],[-42720,39520]],[[0,0,0],[0,0,0],[0,0]],[[-5248800,-4523040,150560],[-4523040,1213120,48640],[150560,48640]],[[0,0,0],[0,0,0],[0,0]],[[-62920800,-13317120,854080],[-13317120,4076320,21280],[854080,21280]],[[0,0,0],[0,0,0],[0,0]],[[-333192960,-13228640,1590880],[-13228640,6392000,3040],[1590880,3040]],[[0,0,0],[0,0],[0]],[[-1026194400,20431040,1533440],[20431040,5584000],[1533440]],[[0,0,0],[0,0],[0]],[[-2020268640,82523680,840160],[82523680,2859840],[840160]],[[0,0,0],[0,0],[0]],[[-2586756160,125051200,263360],[125051200,852000],[263360]],[[0,0,0],[0,0],[0]],[[-1976037120,113686240,44000],[113686240,136640],[44000]],[[0,0,0],[0,0],[0]],[[-405841760,68190880,3040],[68190880,9120],[3040]],[[0,0],[0]],[[1018213760,27677120],[27677120]],[[0,0],[0]],[[1481628800,7537600],[7537600]],[[0,0],[0]],[[1131130240,1320960],[1320960]],[[0,0],[0]],[[579481440,134720],[134720]],[[0,0],[0]],[[210813600,6080],[6080]],[[0]],[[54926400]],[[0]],[[10057600]],[[0]],[[1231840]],[[0]],[[90720]],[[0]],[[3040]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
