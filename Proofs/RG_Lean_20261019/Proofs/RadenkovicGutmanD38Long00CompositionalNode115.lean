/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode113
import Proofs.RadenkovicGutmanD38Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1444]],[[0,0],[0,0,0],[0,0]],[[0,0,12996],[0,0,25992],[12996,25992]],[[0,0,0],[0,0,0],[0,0]],[[116964,233928,229596],[233928,467856,69312],[229596,69312]],[[0,0,0],[0,0,0],[0,0]],[[4132728,4756536,1006468],[4756536,2495232,63536],[1006468,63536]],[[0,0,0],[0,0,0],[0,0]],[[54622188,29708856,2064920],[29708856,5614272,23104],[2064920,23104]],[[0,0,0],[0,0,0],[0,0]],[[357225384,95789184,2373936],[95789184,6931200,2888],[2373936,2888]],[[0,0,0],[0,0],[0]],[[1400883604,189831128,1640384],[189831128,5117536],[1640384]],[[0,0,0],[0,0],[0]],[[3662937040,250895000,694564],[250895000,2310400],[694564]],[[0,0,0],[0,0],[0]],[[6796246648,230745424,176168],[230745424,623808],[176168]],[[0,0,0],[0,0],[0]],[[9300194632,150799808,24548],[150799808,92416],[24548]],[[0,0,0],[0,0],[0]],[[9618934528,70452760,1444],[70452760,5776],[1444]],[[0,0],[0]],[[7633446080,23349480],[23349480]],[[0,0],[0]],[[4685722240,5357240],[5357240]],[[0,0],[0]],[[2229510008,808640],[808640]],[[0,0],[0]],[[819182644,72200],[72200]],[[0,0],[0]],[[229994544,2888],[2888]],[[0]],[[48388440]],[[0]],[[7378840]],[[0]],[[769652]],[[0]],[[49096]],[[0]],[[1444]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
