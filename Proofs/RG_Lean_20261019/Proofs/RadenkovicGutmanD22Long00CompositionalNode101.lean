/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode051
import Proofs.RadenkovicGutmanD22Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,484]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,11616],[0,11616,44]],[[0,0,0],[0,0,0],[0,0]],[[-39204,26136,65340],[26136,262152,36608],[65340,36608]],[[0,0,0],[0,0,0],[0,0]],[[-205524,1758240,395604],[1758240,1589280,38896],[395604,38896]],[[0,0,0],[0,0,0],[0,0]],[[9652500,14502312,994752],[14502312,4002328,16456],[994752,16456]],[[0,0,0],[0,0,0],[0,0]],[[115245636,55608872,1356344],[55608872,5465680,2640],[1356344,2640]],[[0,0,0],[0,0,0],[0,0]],[[608643860,126344592,1097272],[126344592,4428160,88],[1097272,88]],[[0,0,0],[0,0],[0]],[[1947719884,187984192,541376],[187984192,2187504],[541376]],[[0,0,0],[0,0],[0]],[[4234064648,192534936,160864],[192534936,650584],[160864]],[[0,0,0],[0,0],[0]],[[6626827064,139175608,27016],[139175608,109296],[27016]],[[0,0,0],[0,0],[0]],[[7721807192,71639656,2156],[71639656,8712],[2156]],[[0,0,0],[0,0],[0]],[[6833389728,26137672,44],[26137672,176],[44]],[[0,0],[0]],[[4643377200,6625960],[6625960]],[[0,0],[0]],[[2432930720,1118656],[1118656]],[[0,0],[0]],[[980979428,115632],[115632]],[[0,0],[0]],[[301772460,6072],[6072]],[[0,0],[0]],[[69632904,88],[88]],[[0]],[[11706200]],[[0]],[[1364660]],[[0]],[[100892]],[[0]],[[3916]],[[0]],[[44]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
