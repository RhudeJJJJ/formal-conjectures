/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode081
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e084 : NestedArithmetic.Expr 3 := .scaled (-1) e081
noncomputable def p084 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,3456,0],[3456,576,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[57024,50112,0],[50112,4992,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[931392,308736,0],[308736,16960,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[6766848,1069760,0],[1069760,29312,0],[0,0]],[[0,0,0],[0,0],[0]],[[29071680,2331648,0],[2331648,28416],[0]],[[0,0,0],[0,0],[0]],[[82888256,3393088,0],[3393088,16000],[0]],[[0,0,0],[0,0],[0]],[[166897536,3412224,0],[3412224,5184],[0]],[[0,0,0],[0,0],[0]],[[246471424,2415872,0],[2415872,896],[0]],[[0,0,0],[0,0],[0]],[[273468096,1211520,0],[1211520,64],[0]],[[0,0],[0]],[[231432576,427456],[427456]],[[0,0],[0]],[[150641280,103680],[103680]],[[0,0],[0]],[[75607552,16448],[16448]],[[0,0],[0]],[[29165248,1536],[1536]],[[0,0],[0]],[[8560448,64],[64]],[[0]],[[1875840]],[[0]],[[296960]],[[0]],[[32064]],[[0]],[[2112]],[[0]],[[64]]]
theorem step084 : p084=NestedHorner.scale (-1) p081 := by decide +kernel
#print axioms step084
theorem h084 : NestedArithmetic.compile e084=p084 := StagedExprCompile.compile_scaled (-1) e084 e081 p081 p084 rfl h081 step084
#print axioms h084
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
