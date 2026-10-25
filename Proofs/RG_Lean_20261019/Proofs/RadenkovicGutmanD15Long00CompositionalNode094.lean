/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode035
import Proofs.RadenkovicGutmanD15Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-2025],[0,-4050,1170],[-2025,1170]],[[0,0,0],[0,0,0],[0,0]],[[0,-56295,-7020],[-56295,7020,5070],[-7020,5070]],[[0,0,0],[0,0,0],[0,0]],[[-357210,-326025,14085],[-326025,175590,6240],[14085,6240]],[[0,0,0],[0,0,0],[0,0]],[[-2796930,-60075,100530],[-60075,608220,2730],[100530,2730]],[[0,0,0],[0,0,0],[0,0]],[[-3767310,4225710,195330],[4225710,981120,390],[195330,390]],[[0,0,0],[0,0],[0]],[[38036520,15870465,191790],[15870465,879660],[191790]],[[0,0,0],[0,0],[0]],[[229637520,30235095,106185],[30235095,461190],[106185]],[[0,0,0],[0,0],[0]],[[660312060,36078600,33510],[36078600,140340],[33510]],[[0,0,0],[0,0],[0]],[[1220876490,28918755,5625],[28918755,22950],[5625]],[[0,0,0],[0,0],[0]],[[1591772910,15993405,390],[15993405,1560],[390]],[[0,0],[0]],[[1527050460,6122460],[6122460]],[[0,0],[0]],[[1101685410,1593675],[1593675]],[[0,0],[0]],[[603682950,269235],[269235]],[[0,0],[0]],[[251534580,26625],[26625]],[[0,0],[0]],[[79119600,1170],[1170]],[[0]],[[18467640]],[[0]],[[3099390]],[[0]],[[353430]],[[0]],[[24510]],[[0]],[[780]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
