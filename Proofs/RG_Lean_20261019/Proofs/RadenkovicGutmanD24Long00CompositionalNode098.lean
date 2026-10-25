/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode097
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e098 : NestedArithmetic.Expr 3 := .scaled (-1) e097
noncomputable def p098 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1728],[0,1728]],[[0,0,0],[0,0,0],[0,0]],[[0,-15552,25920],[-15552,77760,7632],[25920,7632]],[[0,0,0],[0,0,0],[0,0]],[[-233280,514512,200016],[514512,574992,9840],[200016,9840]],[[0,0,0],[0,0,0],[0,0]],[[1341360,6279120,615024],[6279120,1693152,4800],[615024,4800]],[[0,0,0],[0,0,0],[0,0]],[[39539664,29552544,988704],[29552544,2623056,912],[988704,912]],[[0,0,0],[0,0,0],[0,0]],[[275401728,77927376,914160],[77927376,2355936,48],[914160,48]],[[0,0,0],[0,0],[0]],[[1044611856,130677120,502272],[130677120,1267776],[502272]],[[0,0,0],[0,0],[0]],[[2574798864,147942384,162768],[147942384,405792],[162768]],[[0,0,0],[0,0],[0]],[[4457295840,116503776,29280],[116503776,72912],[29280]],[[0,0,0],[0,0],[0]],[[5652384768,64576848,2448],[64576848,6240],[2448]],[[0,0,0],[0,0],[0]],[[5380849104,25126704,48],[25126704,144],[48]],[[0,0],[0]],[[3898429632,6736416],[6736416]],[[0,0],[0]],[[2162360448,1193472],[1193472]],[[0,0],[0]],[[917527104,128352],[128352]],[[0,0],[0]],[[295511472,6912],[6912]],[[0,0],[0]],[[71064720,96],[96]],[[0]],[[12396960]],[[0]],[[1492800]],[[0]],[[113328]],[[0]],[[4464]],[[0]],[[48]]]
theorem step098 : p098=NestedHorner.scale (-1) p097 := by decide +kernel
#print axioms step098
theorem h098 : NestedArithmetic.compile e098=p098 := StagedExprCompile.compile_scaled (-1) e098 e097 p097 p098 rfl h097 step098
#print axioms h098
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
