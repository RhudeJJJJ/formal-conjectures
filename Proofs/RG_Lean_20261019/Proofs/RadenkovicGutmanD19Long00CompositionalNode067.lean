/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode043
import Proofs.RadenkovicGutmanD19Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,3249],[0,6498,-3876],[3249,-3876,1156]],[[0,0,0],[0,0,0],[0,0]],[[0,111321,-6726],[111321,-79854,4012],[-6726,4012]],[[0,0,0],[0,0,0],[0,0]],[[770796,340659,-54887],[340659,-381706,34816],[-54887,34816]],[[0,0,0],[0,0,0],[0,0]],[[4642272,-1051101,-9694],[-1051101,-270342,41820],[-9694,41820]],[[0,0,0],[0,0,0],[0,0]],[[-1289790,-6506864,305872],[-6506864,1074212,17204],[305872,17204]],[[0,0,0],[0,0,0],[0,0]],[[-95639634,-10563869,655738],[-10563869,2608508,2312],[655738,2312]],[[0,0,0],[0,0],[0]],[[-415707786,376767,641309],[376767,2600254],[641309]],[[0,0,0],[0,0],[0]],[[-954707464,26850188,346006],[26850188,1404210],[346006]],[[0,0,0],[0,0],[0]],[[-1365467722,47366887,105829],[47366887,427830],[105829]],[[0,0,0],[0,0],[0]],[[-1219210304,44989297,17204],[44989297,69190],[17204]],[[0,0,0],[0,0],[0]],[[-539644500,27295976,1156],[27295976,4624],[1156]],[[0,0],[0]],[[168647190,11055185],[11055185]],[[0,0],[0]],[[480771514,2984733],[2984733]],[[0,0],[0]],[[412374430,516811],[516811]],[[0,0],[0]],[[220267782,51986],[51986]],[[0,0],[0]],[[81464916,2312],[2312]],[[0]],[[21330330]],[[0]],[[3901140]],[[0]],[[475548]],[[0]],[[34782]],[[0]],[[1156]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
