/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode035
import Proofs.RadenkovicGutmanD17Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-2601],[0,-5202,1530],[-2601,1530]],[[0,0,0],[0,0,0],[0,0]],[[0,-72063,-8772],[-72063,9996,6630],[-8772,6630]],[[0,0,0],[0,0,0],[0,0]],[[-454410,-408969,19805],[-408969,232390,8160],[19805,8160]],[[0,0,0],[0,0,0],[0,0]],[[-3483810,4437,133858],[4437,800156,3570],[133858,3570]],[[0,0,0],[0,0,0],[0,0]],[[-3867534,5750590,257754],[5750590,1287648,510],[257754,510]],[[0,0,0],[0,0],[0]],[[53573256,21139313,252110],[21139313,1152940],[252110]],[[0,0,0],[0,0],[0]],[[309546336,39982487,139281],[39982487,603942],[139281]],[[0,0,0],[0,0],[0]],[[879313916,47533496,43894],[47533496,183668],[43894]],[[0,0,0],[0,0],[0]],[[1616441226,38013819,7361],[38013819,30022],[7361]],[[0,0,0],[0,0],[0]],[[2100369278,20990869,510],[20990869,2040],[510]],[[0,0],[0]],[[2010447948,8026516],[8026516]],[[0,0],[0]],[[1448110898,2087515],[2087515]],[[0,0],[0]],[[792558598,352427],[352427]],[[0,0],[0]],[[329923828,34833],[34833]],[[0,0],[0]],[[103698912,1530],[1530]],[[0]],[[24189912]],[[0]],[[4057662]],[[0]],[[462502]],[[0]],[[32062]],[[0]],[[1020]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
