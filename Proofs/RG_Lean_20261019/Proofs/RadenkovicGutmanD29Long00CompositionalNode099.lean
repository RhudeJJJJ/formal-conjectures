/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode096
import Proofs.RadenkovicGutmanD29Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,5046],[0,5046,-1566]],[[0,0,0],[0,0,0],[0,0]],[[0,0,60552],[0,206451,-6148],[60552,-6148]],[[0,0,0],[0,0,0],[0,0]],[[213759,1677969,323814],[1677969,984840,-47502],[323814,-47502]],[[0,0,0],[0,0,0],[0,0]],[[14729013,14654628,658184],[14654628,1575367,-56202],[658184,-56202]],[[0,0,0],[0,0,0],[0,0]],[[159321708,55770219,551754],[55770219,372012,-22968],[551754,-22968]],[[0,0,0],[0,0,0],[0,0]],[[833028567,120790046,-18734],[120790046,-1865512,-3074],[-18734,-3074]],[[0,0,0],[0,0],[0]],[[2659108919,162642005,-393530],[162642005,-2593122],[-393530]],[[0,0,0],[0,0],[0]],[[5723854120,137966224,-313548],[137966224,-1590505],[-313548]],[[0,0,0],[0,0],[0]],[[8745141980,67923626,-114898],[67923626,-519912],[-114898]],[[0,0,0],[0,0],[0]],[[9740644381,10366108,-20822],[10366108,-88073],[-20822]],[[0,0,0],[0,0],[0]],[[7989171256,-9720713,-1508],[-9720713,-6090],[-1508]],[[0,0],[0]],[[4793035842,-7751004],[-7751004]],[[0,0],[0]],[[2033871964,-2770109],[-2770109]],[[0,0],[0]],[[547724073,-562890],[-562890]],[[0,0],[0]],[[49594031,-62901],[-62901]],[[0,0],[0]],[[-28247856,-3016],[-3016]],[[0]],[[-14781880]],[[0]],[[-3602989]],[[0]],[[-517157]],[[0]],[[-42079]],[[0]],[[-1508]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
