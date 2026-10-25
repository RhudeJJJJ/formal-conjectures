/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode110
import Proofs.RadenkovicGutmanD8Long00CompositionalNode111
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e112 : NestedArithmetic.Expr 3 := .plus e110 e111
noncomputable def p112 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,64]],[[0,0],[0,0,0],[0,0,0]],[[0,0,576],[0,0,1344],[576,1344,176]],[[0,0,0],[0,0,0],[0,0,0]],[[5184,12096,14208],[12096,27936,7264],[14208,7264,4]],[[0,0,0],[0,0,0],[0,0]],[[244080,325728,92656],[325728,225480,13192],[92656,13192]],[[0,0,0],[0,0,0],[0,0]],[[4132836,2718504,281220],[2718504,745376,10432],[281220,10432]],[[0,0,0],[0,0,0],[0,0]],[[34169160,11590360,477120],[11590360,1342600,3632],[477120,3632]],[[0,0,0],[0,0,0],[0,0]],[[167727340,30132600,490608],[30132600,1461648,480],[490608,480]],[[0,0,0],[0,0,0],[0,0]],[[544835352,52065504,316640],[52065504,1001376,8],[316640,8]],[[0,0,0],[0,0],[0]],[[1249249716,62683064,128920],[62683064,433744],[128920]],[[0,0,0],[0,0],[0]],[[2106109552,53978584,32256],[53978584,115528],[32256]],[[0,0,0],[0,0],[0]],[[2681285080,33665232,4592],[33665232,17488],[4592]],[[0,0,0],[0,0],[0]],[[2622960776,15228704,304],[15228704,1224],[304]],[[0,0,0],[0,0],[0]],[[1992857728,4948216,4],[4948216,16],[4]],[[0,0],[0]],[[1182242752,1127496],[1127496]],[[0,0],[0]],[[547855776,171960],[171960]],[[0,0],[0]],[[197392616,16032],[16032]],[[0,0],[0]],[[54709716,744],[744]],[[0,0],[0]],[[11448144,8],[8]],[[0]],[[1753656]],[[0]],[[186760]],[[0]],[[12596]],[[0]],[[440]],[[0]],[[4]]]
theorem step112 : p112=NestedHorner.add p110 p111 := by decide +kernel
#print axioms step112
theorem h112 : NestedArithmetic.compile e112=p112 := StagedExprCompile.compile_plus e112 e110 e111 p110 p111 p112 rfl h110 h111 step112
#print axioms h112
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
