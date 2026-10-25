/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode033
import Proofs.RadenkovicGutmanD30Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,900]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,21600],[0,21600,60]],[[0,0,0],[0,0,0],[0,0]],[[-72900,-48600,121500],[-48600,469800,67680],[121500,67680]],[[0,0,0],[0,0,0],[0,0]],[[-1997460,1846800,733860],[1846800,2795040,71280],[733860,71280]],[[0,0,0],[0,0,0],[0,0]],[[-8564940,18101880,1840320],[18101880,6884280,29640],[1840320,29640]],[[0,0,0],[0,0,0],[0,0]],[[20629620,72334440,2500920],[72334440,9179280,4560],[2500920,4560]],[[0,0,0],[0,0,0],[0,0]],[[295118100,166440960,2014200],[166440960,7257600,120],[2014200,120]],[[0,0,0],[0,0],[0]],[[1222851180,248684400,987360],[248684400,3499440],[987360]],[[0,0,0],[0,0],[0]],[[3014784840,255238200,290400],[255238200,1015800],[290400]],[[0,0,0],[0,0],[0]],[[5103897240,184913640,47880],[184913640,166320],[47880]],[[0,0,0],[0,0],[0]],[[6297146520,95472120,3660],[95472120,12840],[3660]],[[0,0,0],[0,0],[0]],[[5835911520,34967880,60],[34967880,240],[60]],[[0,0],[0]],[[4126843920,8904600],[8904600]],[[0,0],[0]],[[2241354720,1510800],[1510800]],[[0,0],[0]],[[934304100,156960],[156960]],[[0,0],[0]],[[296605260,8280],[8280]],[[0,0],[0]],[[70556040,120],[120]],[[0]],[[12226680]],[[0]],[[1471380]],[[0]],[[112860]],[[0]],[[4620]],[[0]],[[60]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
