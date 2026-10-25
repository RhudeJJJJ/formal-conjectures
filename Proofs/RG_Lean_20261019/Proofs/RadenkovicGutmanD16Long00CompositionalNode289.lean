/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode217
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e289 : NestedArithmetic.Expr 3 := .pow e217 2
noncomputable def p289 : NestedHorner.Poly 3 := [[[1024],[0],[0]],[[0,0],[0,0],[0]],[[30720,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[422912,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[3540992,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[20150272,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[82499584,1024,0],[1024,0],[0]],[[0,0,0],[0,0],[0]],[[250964992,22528,0],[22528,0],[0]],[[0,0,0],[0,0],[0]],[[577660928,220160,0],[220160,0],[0]],[[0,0,0],[0,0],[0]],[[1015113728,1259520,0],[1259520,0],[0]],[[0,0,0],[0,0],[0]],[[1364256768,4680704,0],[4680704,0],[0]],[[0,0,0],[0,0],[0]],[[1395395584,11857920,256],[11857920,512],[256]],[[0,0,0],[0,0],[0]],[[1073092608,20916224,3584],[20916224,7168],[3584]],[[0,0,0],[0,0],[0]],[[607205376,25784320,20736],[25784320,41472],[20736]],[[0,0,0],[0,0],[0]],[[243910656,21965824,64000],[21965824,128000],[64000]],[[0,0,0],[0,0],[0]],[[65442816,12564480,113664],[12564480,227328],[113664]],[[0,0,0],[0,0],[0]],[[10450944,4561920,117248],[4561920,234496],[117248]],[[0,0,0],[0,0],[0]],[[746496,940032,67840],[940032,135680],[67840]],[[0,0,0],[0,0],[0]],[[0,82944,19968],[82944,39936],[19968]],[[0,0,0],[0,0],[0]],[[0,0,2304],[0,4608],[2304]]]
theorem step289 : p289=NestedArithmetic.power p217 2 := by decide +kernel
#print axioms step289
theorem h289 : NestedArithmetic.compile e289=p289 := StagedExprCompile.compile_pow 2 e289 e217 p217 p289 rfl h217 step289
#print axioms h289
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
