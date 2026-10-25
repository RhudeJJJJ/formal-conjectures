/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode093
import Proofs.RadenkovicGutmanD41Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1681]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-15129],[0,-30258,49938],[-15129,49938,82]],[[0,0,0],[0,0,0],[0,0]],[[-136161,-503685,182163],[-503685,960630,167444],[182163,167444]],[[0,0,0],[0,0,0],[0,0]],[[-6258978,1320651,1527209],[1320651,6737530,182860],[1527209,182860]],[[0,0,0],[0,0,0],[0,0]],[[-33443577,35876025,4323778],[35876025,17943978,76424],[4323778,76424]],[[0,0,0],[0,0,0],[0,0]],[[40969824,176448584,6316460],[176448584,25218772,11234],[6316460,11234]],[[0,0,0],[0,0,0],[0,0]],[[982682957,451846445,5339676],[451846445,20706476,164],[5339676,164]],[[0,0,0],[0,0],[0]],[[4451246016,723681939,2701531],[723681939,10237946],[2701531]],[[0,0,0],[0,0],[0]],[[11520211078,779955136,807454],[779955136,3004562],[807454]],[[0,0,0],[0,0],[0]],[[20119087122,585111205,132471],[585111205,486178],[132471]],[[0,0,0],[0,0],[0]],[[25325768880,309418923,9553],[309418923,34850],[9553]],[[0,0,0],[0,0],[0]],[[23754557040,114958342,82],[114958342,328],[82]],[[0,0],[0]],[[16894218018,29396795],[29396795]],[[0,0],[0]],[[9179838910,4941935],[4941935]],[[0,0],[0]],[[3810373909,496469],[496469]],[[0,0],[0]],[[1198792440,23616],[23616]],[[0,0],[0]],[[281030154,164],[164]],[[0]],[[47618302]],[[0]],[[5529383]],[[0]],[[397946]],[[0]],[[14063]],[[0]],[[82]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
