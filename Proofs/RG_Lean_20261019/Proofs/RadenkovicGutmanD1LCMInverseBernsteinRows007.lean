/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinWeights35 : List (Option ℤ) := [some 4199004729209426541557328,some 1670058699117385556301210,some 652666618045874815106220,some 250441841808300801145410,some 94283987504301478078272,some 34795281102777926433648,some 12576607627510093891680,some 4447824648753569790960,some 1537519631667900668480,some 518912875687916475612,some 170781452758048460328,some 54737645114759121900,some 17061084191613232800,some 5163222847461899400,some 1514545368588823824,some 429803415410341896,some 117754360386395040,some 31074067324187580,some 7877932561061640,some 1913212193400684,some 443643407165376,some 97862516286480,some 20448884000160,some 4027810484880,some 743595781824,some 127805525001,some 20286591270,some 2944827765,some 386206920,some 45057474,some 4582116,some 395010,some 27720,some 1485,some 54,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights35_identity : bernsteinWeights35=IntegerWeightedBernstein.weights 88 35 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights35_identity
def bernsteinRow35 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights35 affine01753)
theorem bernsteinRow35_weighted : bernsteinRow35=IntegerWeightedBernstein.applyWeights bernsteinWeights35 affine01753 := by decide +kernel
theorem bernsteinRow35_identity : bernsteinRow35=NestedInteger.coefficientFrom 88 35 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 35 0 affine01753 bernsteinRow35 bernsteinWeights35 bernsteinWeights35_identity bernsteinRow35_weighted
theorem bernsteinRow35_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow35=true := by decide +kernel
#print axioms bernsteinRow35_weighted
#print axioms bernsteinRow35_identity
#print axioms bernsteinRow35_positive
def bernsteinWeights36 : List (Option ℤ) := [some 6181868073558322408403844,some 2528946030092040985256118,some 1017392081071510741194990,some 402224776237574013960810,some 156157854303999323067138,some 59488706401523551644624,some 22218673475267832541968,some 8128782978756524100720,some 2910305017085669122480,some 1018606755979984192868,some 348131422929868015284,some 116043807643289338428,some 37676560923145889100,some 11897861344151333400,some 3648677478873075576,some 1084741953178481928,some 312049055023946856,some 86680293062207460,some 23196134763125940,some 5964720367660956,some 1469568786235308,some 345780890878896,some 77413632286320,some 16421073515280,some 3284214703056,some 615790256823,some 107518933731,some 17341763505,some 2558620845,some 341149446,some 40475358,some 4187106,some 367290,some 26235,some 1431,some 53,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights36_identity : bernsteinWeights36=IntegerWeightedBernstein.weights 88 36 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights36_identity
def bernsteinRow36 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights36 affine01753)
theorem bernsteinRow36_weighted : bernsteinRow36=IntegerWeightedBernstein.applyWeights bernsteinWeights36 affine01753 := by decide +kernel
theorem bernsteinRow36_identity : bernsteinRow36=NestedInteger.coefficientFrom 88 36 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 36 0 affine01753 bernsteinRow36 bernsteinWeights36 bernsteinWeights36_identity bernsteinRow36_weighted
theorem bernsteinRow36_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow36=true := by decide +kernel
#print axioms bernsteinRow36_weighted
#print axioms bernsteinRow36_identity
#print axioms bernsteinRow36_positive
def bernsteinWeights37 : List (Option ℤ) := [some 8688030806081966628027024,some 3652922043466281423147726,some 1511553949020530244061128,some 615167304833936727234180,some 246066921933574690893672,some 96669147902475771422514,some 37270032926255719102656,some 14089890496511308441248,some 5218477961670854978240,some 1891698261105684929612,some 670475333050116177584,some 232087615286578676856,some 78367246720143449328,some 25778699578994555700,some 8249183865278257824,some 2563935525694593648,some 772692898154535072,some 225368761961739396,some 63484158299081520,some 17231414395464984,some 4495151581425648,some 1123787895356412,some 268367258592576,some 60992558771040,some 13136858812224,some 2668424446233,some 508271323092,some 90177170226,some 14783142660,some 2217471399,some 300674088,some 36288252,some 3819816,some 341055,some 24804,some 1378,some 52,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights37_identity : bernsteinWeights37=IntegerWeightedBernstein.weights 88 37 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights37_identity
def bernsteinRow37 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights37 affine01753)
theorem bernsteinRow37_weighted : bernsteinRow37=IntegerWeightedBernstein.applyWeights bernsteinWeights37 affine01753 := by decide +kernel
theorem bernsteinRow37_identity : bernsteinRow37=NestedInteger.coefficientFrom 88 37 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 37 0 affine01753 bernsteinRow37 bernsteinWeights37 bernsteinWeights37_identity bernsteinRow37_weighted
theorem bernsteinRow37_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow37=true := by decide +kernel
#print axioms bernsteinRow37_weighted
#print axioms bernsteinRow37_identity
#print axioms bernsteinRow37_positive
def bernsteinWeights38 : List (Option ℤ) := [some 11660251871320534158667848,some 5035108762615685204879298,some 2141368094445751179086598,some 896386644186593516826948,some 369100382900362036340508,some 149397774031098919471158,some 59399114976220052319858,some 23180142429744410661408,some 8871412534840453463008,some 3326779700565170048628,some 1221222928055568752028,some 438387717763537500728,some 153720368566435227528,some 52588547141148893628,some 17529515713716297876,some 5685248339583664176,some 1791242627540058576,some 547324136192795676,some 161884603662657876,some 46252743903616536,some 12736262814039336,some 3371363686069236,some 855420636763836,some 207374699821536,some 47855699958816,some 10468434365991,some 2160153123141,some 418094152866,some 75394027566,some 12565671261,some 1916797311,some 264385836,some 32468436,some 3478761,some 316251,some 23426,some 1326,some 51,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights38_identity : bernsteinWeights38=IntegerWeightedBernstein.weights 88 38 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights38_identity
def bernsteinRow38 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights38 affine01753)
theorem bernsteinRow38_weighted : bernsteinRow38=IntegerWeightedBernstein.applyWeights bernsteinWeights38 affine01753 := by decide +kernel
theorem bernsteinRow38_identity : bernsteinRow38=NestedInteger.coefficientFrom 88 38 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 38 0 affine01753 bernsteinRow38 bernsteinWeights38 bernsteinWeights38_identity bernsteinRow38_weighted
theorem bernsteinRow38_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow38=true := by decide +kernel
#print axioms bernsteinRow38_weighted
#print axioms bernsteinRow38_identity
#print axioms bernsteinRow38_positive
def bernsteinWeights39 : List (Option ℤ) := [some 14949040860667351485471600,some 6625143108704848953788550,some 2893740668169934025792700,some 1244981450259157662259650,some 527286261286231480486440,some 219702608869263116869350,some 89998659054878867151300,some 36218972546475641658450,some 14308729894903957198400,some 5544632834275283414380,some 2105556772509601296600,some 782835210292031251300,some 284667349197102273200,some 101131821425286333900,some 35059031427432595752,some 11844267374132633700,some 3894005712043605600,some 1243918491347262900,some 385439532530137800,some 115631859759041340,some 33516481089577200,some 9364899127970100,some 2515943049305400,some 648045936942300,some 159518999862720,some 37387265592825,some 8308281242850,some 1742058970275,some 342700125300,some 62828356305,some 10648873950,some 1652411475,some 231917400,some 28989675,some 3162510,some 292825,some 22100,some 1275,some 50,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights39_identity : bernsteinWeights39=IntegerWeightedBernstein.weights 88 39 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights39_identity
def bernsteinRow39 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights39 affine01753)
theorem bernsteinRow39_weighted : bernsteinRow39=IntegerWeightedBernstein.applyWeights bernsteinWeights39 affine01753 := by decide +kernel
theorem bernsteinRow39_identity : bernsteinRow39=NestedInteger.coefficientFrom 88 39 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 39 0 affine01753 bernsteinRow39 bernsteinWeights39 bernsteinWeights39_identity bernsteinRow39_weighted
theorem bernsteinRow39_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow39=true := by decide +kernel
#print axioms bernsteinRow39_weighted
#print axioms bernsteinRow39_identity
#print axioms bernsteinRow39_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
