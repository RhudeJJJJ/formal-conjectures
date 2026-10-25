/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode220
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e221 : NestedArithmetic.Expr 3 := .scaled (-1) e220
noncomputable def p221 : NestedHorner.Poly 3 := [[[512],[0],[0]],[[0,0],[0,0],[0]],[[15872,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[225792,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1953792,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[11492352,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[48647168,768,0],[768,0],[0]],[[0,0,0],[0,0],[0]],[[153041408,17152,0],[17152,0],[0]],[[0,0,0],[0,0],[0]],[[364384768,170240,0],[170240,0],[0]],[[0,0,0],[0,0],[0]],[[662458368,989696,0],[989696,0],[0]],[[0,0,0],[0,0],[0]],[[921077248,3739904,0],[3739904,0],[0]],[[0,0,0],[0,0],[0]],[[974439936,9640704,256],[9640704,512],[256]],[[0,0,0],[0,0],[0]],[[774685696,17314816,3584],[17314816,7168],[3584]],[[0,0,0],[0,0],[0]],[[452760576,21743872,20736],[21743872,41472],[20736]],[[0,0,0],[0,0],[0]],[[187600896,18873088,64000],[18873088,128000],[64000]],[[0,0,0],[0,0],[0]],[[51826176,10995200,113664],[10995200,227328],[113664]],[[0,0,0],[0,0],[0]],[[8501760,4061952,117248],[4061952,234496],[117248]],[[0,0,0],[0,0],[0]],[[622080,850176,67840],[850176,135680],[67840]],[[0,0,0],[0,0],[0]],[[0,76032,19968],[76032,39936],[19968]],[[0,0,0],[0,0],[0]],[[0,0,2304],[0,4608],[2304]]]
theorem step221 : p221=NestedHorner.scale (-1) p220 := by decide +kernel
#print axioms step221
theorem h221 : NestedArithmetic.compile e221=p221 := StagedExprCompile.compile_scaled (-1) e221 e220 p220 p221 rfl h220 step221
#print axioms h221
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
