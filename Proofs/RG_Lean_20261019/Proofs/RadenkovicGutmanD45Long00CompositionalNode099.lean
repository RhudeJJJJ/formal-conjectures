/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode096
import Proofs.RadenkovicGutmanD45Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,12150],[0,12150,-3870]],[[0,0,0],[0,0,0],[0,0]],[[0,0,145800],[0,495315,-16740],[145800,-16740]],[[0,0,0],[0,0,0],[0,0]],[[506655,4022865,770310],[4022865,2318760,-119790],[770310,-119790]],[[0,0,0],[0,0,0],[0,0]],[[35160885,34909380,1532520],[34909380,3535335,-140490],[1532520,-140490]],[[0,0,0],[0,0,0],[0,0]],[[379376460,131841675,1206090],[131841675,328140,-57240],[1206090,-57240]],[[0,0,0],[0,0,0],[0,0]],[[1976963895,282708990,-201870],[282708990,-5184360,-7650],[-201870,-7650]],[[0,0,0],[0,0],[0]],[[6286184055,375038325,-1067130],[375038325,-6749730],[-1067130]],[[0,0,0],[0,0],[0]],[[13469609160,309728880,-810540],[309728880,-4055625],[-810540]],[[0,0,0],[0,0],[0]],[[20463961500,142399530,-292050],[142399530,-1312200],[-292050]],[[0,0,0],[0,0],[0]],[[22626032445,10842300,-52470],[10842300,-220905],[-52470]],[[0,0,0],[0,0],[0]],[[18364512600,-30131145,-3780],[-30131145,-15210],[-3780]],[[0,0],[0]],[[10836913410,-20932380],[-20932380]],[[0,0],[0]],[[4458260700,-7199325],[-7199325]],[[0,0],[0]],[[1106865225,-1436490],[-1436490]],[[0,0],[0]],[[40450095,-158805],[-158805]],[[0,0],[0]],[[-90475920,-7560],[-7560]],[[0]],[[-40375800]],[[0]],[[-9413325]],[[0]],[[-1323045]],[[0]],[[-106335]],[[0]],[[-3780]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
