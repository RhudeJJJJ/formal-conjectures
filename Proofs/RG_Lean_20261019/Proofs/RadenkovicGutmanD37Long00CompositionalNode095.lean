/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode093
import Proofs.RadenkovicGutmanD37Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1369]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-12321],[0,-24642,40626],[-12321,40626,74]],[[0,0,0],[0,0,0],[0,0]],[[-110889,-410589,147963],[-410589,780774,136308],[147963,136308]],[[0,0,0],[0,0,0],[0,0]],[[-5104890,1059939,1241609],[1059939,5478442,149036],[1241609,149036]],[[0,0,0],[0,0,0],[0,0]],[[-27419553,29097873,3516850],[29097873,14595834,62456],[3516850,62456]],[[0,0,0],[0,0,0],[0,0]],[[31787736,143269032,5140188],[143269032,20522420,9250],[5140188,9250]],[[0,0,0],[0,0,0],[0,0]],[[792927797,367082069,4348092],[367082069,16861196,148],[4348092,148]],[[0,0,0],[0,0],[0]],[[3603246776,588176235,2201907],[588176235,8344906],[2201907]],[[0,0,0],[0,0],[0]],[[9337542518,634184144,659118],[634184144,2453026],[659118]],[[0,0,0],[0,0],[0]],[[16319836050,475986685,108447],[475986685,398194],[108447]],[[0,0,0],[0,0],[0]],[[20555155824,251862515,7881],[251862515,28786],[7881]],[[0,0,0],[0,0],[0]],[[19289578224,93648998,74],[93648998,296],[74]],[[0,0],[0]],[[13725406706,23975075],[23975075]],[[0,0],[0]],[[7461843502,4037847],[4037847]],[[0,0],[0]],[[3099088957,407037],[407037]],[[0,0],[0]],[[975712496,19536],[19536]],[[0,0],[0]],[[228948378,148],[148]],[[0]],[[38844894]],[[0]],[[4520031]],[[0]],[[326562]],[[0]],[[11655]],[[0]],[[74]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
