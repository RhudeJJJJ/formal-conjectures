/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode033
import Proofs.RadenkovicGutmanD6Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,108],[0,108]],[[0,0,0],[0,0,0],[0,0]],[[0,-972,972],[-972,3564,468],[972,468]],[[0,0,0],[0,0,0],[0,0]],[[-14580,10692,6804],[10692,24408,576],[6804,576]],[[0,0,0],[0,0,0],[0,0]],[[-92340,150336,18792],[150336,65628,252],[18792,252]],[[0,0,0],[0,0,0],[0,0]],[[50544,680364,27252],[680364,92520,36],[27252,36]],[[0,0,0],[0,0],[0]],[[2378268,1684584,22896],[1684584,75600],[22896]],[[0,0,0],[0,0],[0]],[[11305044,2646396,11484],[2646396,36936],[11484]],[[0,0,0],[0,0],[0]],[[29922120,2815704,3384],[2815704,10620],[3384]],[[0,0,0],[0,0],[0]],[[53112240,2092644,540],[2092644,1656],[540]],[[0,0,0],[0,0],[0]],[[67833900,1098252,36],[1098252,108],[36]],[[0,0],[0]],[[64522800,405000],[405000]],[[0,0],[0]],[[46520784,102600],[102600]],[[0,0],[0]],[[25611552,16992],[16992]],[[0,0],[0]],[[10759860,1656],[1656]],[[0,0],[0]],[[3420468,72],[72]],[[0]],[[808056]],[[0]],[[137376]],[[0]],[[15876]],[[0]],[[1116]],[[0]],[[36]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
