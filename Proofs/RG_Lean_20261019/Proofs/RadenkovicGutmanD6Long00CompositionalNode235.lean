/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode213
import Proofs.RadenkovicGutmanD6Long00CompositionalNode219
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e235 : NestedArithmetic.Expr 3 := .times e213 e219
noncomputable def p235 : NestedHorner.Poly 3 := [[[36],[0],[0]],[[0,0],[0,0],[0]],[[1116,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[15876,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[137376,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[808056,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[3420468,72,0],[72,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[10759860,1656,0],[1656,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[25611552,16992,0],[16992,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[46520784,102600,0],[102600,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[64522800,405000,0],[405000,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[67833900,1098252,36],[1098252,108,0],[36,0]],[[0,0,0],[0,0,0],[0,0]],[[53112240,2092644,540],[2092644,1656,0],[540,0]],[[0,0,0],[0,0,0],[0,0]],[[29922120,2815704,3384],[2815704,10620,0],[3384,0]],[[0,0,0],[0,0,0],[0,0]],[[11305044,2646396,11484],[2646396,36936,0],[11484,0]],[[0,0,0],[0,0,0],[0,0]],[[2378268,1684584,22896],[1684584,75600,0],[22896,0]],[[0,0,0],[0,0,0],[0,0]],[[50544,680364,27252],[680364,92520,36],[27252,36]],[[0,0,0],[0,0,0],[0,0]],[[-92340,150336,18792],[150336,65628,252],[18792,252]],[[0,0,0],[0,0,0],[0,0]],[[-14580,10692,6804],[10692,24408,576],[6804,576]],[[0,0,0],[0,0,0],[0,0]],[[0,-972,972],[-972,3564,468],[972,468]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,108],[0,108]]]
theorem step235 : p235=NestedArithmetic.mul p213 p219 := by decide +kernel
#print axioms step235
theorem h235 : NestedArithmetic.compile e235=p235 := StagedExprCompile.compile_times e235 e213 e219 p213 p219 p235 rfl h213 h219 step235
#print axioms h235
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
