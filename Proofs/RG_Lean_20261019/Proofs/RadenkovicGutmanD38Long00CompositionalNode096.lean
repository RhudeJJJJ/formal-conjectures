/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode043
import Proofs.RadenkovicGutmanD38Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,4332],[0,4332,-2736]],[[0,0,0],[0,0,0],[0,0]],[[0,38988,38988],[38988,158688,-30476],[38988,-30476]],[[0,0,0],[0,0,0],[0,0]],[[948024,1584144,51300],[1584144,228912,-108224],[51300,-108224]],[[0,0,0],[0,0,0],[0,0]],[[21800448,9285984,-428184],[9285984,-1632176,-110276],[-428184,-110276]],[[0,0,0],[0,0,0],[0,0]],[[172852272,20868232,-1566284],[20868232,-6125904,-42332],[-1566284,-42332]],[[0,0,0],[0,0,0],[0,0]],[[730012224,9554568,-2364816],[9554568,-9324288,-5472],[-2364816,-5472]],[[0,0,0],[0,0],[0]],[[1909591960,-53072624,-1963460],[-53072624,-7777840],[-1963460]],[[0,0,0],[0,0],[0]],[[3278678304,-140011000,-958664],[-140011000,-3810032],[-958664]],[[0,0,0],[0,0],[0]],[[3671707136,-180774892,-273828],[-180774892,-1091056],[-273828]],[[0,0,0],[0,0],[0]],[[2329382216,-147452844,-42332],[-147452844,-169024],[-42332]],[[0,0,0],[0,0],[0]],[[1733864,-81197868,-2736],[-81197868,-10944],[-2736]],[[0,0],[0]],[[-1718064360,-30681960],[-30681960]],[[0,0],[0]],[[-2033049856,-7856044],[-7856044]],[[0,0],[0]],[[-1408078448,-1304008],[-1304008]],[[0,0],[0]],[[-672985016,-126692],[-126692]],[[0,0],[0]],[[-231395376,-5472],[-5472]],[[0]],[[-57431680]],[[0]],[[-10073496]],[[0]],[[-1186816]],[[0]],[[-84360]],[[0]],[[-2736]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
