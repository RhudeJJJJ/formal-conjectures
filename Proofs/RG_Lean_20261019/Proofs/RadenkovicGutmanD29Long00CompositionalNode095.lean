/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode093
import Proofs.RadenkovicGutmanD29Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,841]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-7569],[0,-15138,24882],[-7569,24882,58]],[[0,0,0],[0,0,0],[0,0]],[[-68121,-252909,90219],[-252909,476934,83636],[90219,83636]],[[0,0,0],[0,0,0],[0,0]],[[-3149226,624051,759017],[624051,3350602,91756],[759017,91756]],[[0,0,0],[0,0,0],[0,0]],[[-17162577,17667873,2152786],[17667873,8935770,38744],[2152786,38744]],[[0,0,0],[0,0,0],[0,0]],[[16786824,87265640,3150908],[87265640,12580084,5858],[3150908,5858]],[[0,0,0],[0,0,0],[0,0]],[[474314981,223941509,2670204],[223941509,10354508,116],[2670204,116]],[[0,0,0],[0,0],[0]],[[2175614568,359263803,1355779],[359263803,5138858],[1355779]],[[0,0,0],[0,0],[0]],[[5658959254,387838576,407566],[387838576,1517570],[407566]],[[0,0,0],[0,0],[0]],[[9912520914,291493645,67599],[291493645,248530],[67599]],[[0,0,0],[0,0],[0]],[[12505695984,154502691,5017],[154502691,18386],[5017]],[[0,0,0],[0,0],[0]],[[11752568304,57577702,58],[57577702,232],[58]],[[0,0],[0]],[[8374115922,14788115],[14788115]],[[0,0],[0]],[[4559302222,2503367],[2503367]],[[0,0],[0]],[[1896761965,254765],[254765]],[[0,0],[0]],[[598390176,12528],[12528]],[[0,0],[0]],[[140783226,116],[116]],[[0]],[[23975518]],[[0]],[[2806127]],[[0]],[[204914]],[[0]],[[7511]],[[0]],[[58]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
