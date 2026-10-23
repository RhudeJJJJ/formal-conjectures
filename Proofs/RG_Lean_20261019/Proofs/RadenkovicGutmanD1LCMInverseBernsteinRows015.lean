/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinWeights75 : List (Option ℤ) := [some 1200635647008336,some 1023269017336650,some 870366750378300,some 738799683460650,some 625806790696080,some 528955739755020,some 446107250395800,some 375382930211100,some 315136287090800,some 263926640438545,some 220495674290430,some 183746395242025,some 152724276564800,some 126600387152400,some 104656320045984,some 86270750308176,some 70907466006720,some 58104729088840,some 47465835030320,some 38650751381832,some 31368725759168,some 25371763481680,some 20448884000160,some 16421073515280,some 13136858812224,some 10468434365991,some 8308281242850,some 6566222272575,some 5166863427600,some 4047376351620,some 3155581562280,some 2448296039700,some 1889912732400,some 1451182990950,some 1108176102180,some 841392966470,some 635013559600,some 476260169700,some 354860518600,some 262596783764,some 192928249296,some 140676848445,some 101766230790,some 73006209045,some 51915526432,some 36576848168,some 25518731280,some 17620076360,some 12033222880,some 8122425444,some 5414950296,some 3562467300,some 2310789600,some 1476337800,some 927983760,some 573166440,some 347373600,some 206253075,some 119759850,some 67863915,some 37442160,some 20058300,some 10400600,some 5200300,some 2496144,some 1144066,some 497420,some 203490,some 77520,some 27132,some 8568,some 2380,some 560,some 105,some 14,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights75_identity : bernsteinWeights75=IntegerWeightedBernstein.weights 88 75 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights75_identity
def bernsteinRow75 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights75 affine01753)
theorem bernsteinRow75_weighted : bernsteinRow75=IntegerWeightedBernstein.applyWeights bernsteinWeights75 affine01753 := by decide +kernel
theorem bernsteinRow75_identity : bernsteinRow75=NestedInteger.coefficientFrom 88 75 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 75 0 affine01753 bernsteinRow75 bernsteinWeights75 bernsteinWeights75_identity bernsteinRow75_weighted
theorem bernsteinRow75_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow75=true := by decide +kernel
#print axioms bernsteinRow75_weighted
#print axioms bernsteinRow75_identity
#print axioms bernsteinRow75_positive
def bernsteinWeights76 : List (Option ℤ) := [some 205371886988268,some 177366629671686,some 152902266958350,some 131567066917650,some 112992892764570,some 96851050941060,some 82848489359220,some 70724320184700,some 60246643120300,some 51209646652255,some 43430966148115,some 36749279048405,some 31022118677225,some 26123889412400,some 21944067106416,some 18385569737808,some 15363284301456,some 12802736917880,some 10638894058520,some 8815083648488,some 7282025622664,some 5996962277488,some 4922879481520,some 4027810484880,some 3284214703056,some 2668424446233,some 2160153123141,some 1742058970275,some 1399358844975,some 1119487075980,some 891794789340,some 707285522580,some 558383307300,some 438729741450,some 343006888770,some 266783135710,some 206379406870,some 158753389900,some 121399651100,some 92263734836,some 69668534468,some 52251400851,some 38910617655,some 28760021745,some 21090682613,some 15338678264,some 11058116888,some 7898654920,some 5586853480,some 3910797436,some 2707475148,some 1852482996,some 1251677700,some 834451800,some 548354040,some 354817320,some 225792840,some 141120525,some 86493225,some 51895935,some 30421755,some 17383860,some 9657700,some 5200300,some 2704156,some 1352078,some 646646,some 293930,some 125970,some 50388,some 18564,some 6188,some 1820,some 455,some 91,some 13,some 1,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights76_identity : bernsteinWeights76=IntegerWeightedBernstein.weights 88 76 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights76_identity
def bernsteinRow76 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights76 affine01753)
theorem bernsteinRow76_weighted : bernsteinRow76=IntegerWeightedBernstein.applyWeights bernsteinWeights76 affine01753 := by decide +kernel
theorem bernsteinRow76_identity : bernsteinRow76=NestedInteger.coefficientFrom 88 76 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 76 0 affine01753 bernsteinRow76 bernsteinWeights76 bernsteinWeights76_identity bernsteinRow76_weighted
theorem bernsteinRow76_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow76=true := by decide +kernel
#print axioms bernsteinRow76_weighted
#print axioms bernsteinRow76_identity
#print axioms bernsteinRow76_positive
def bernsteinWeights77 : List (Option ℤ) := [some 32006008361808,some 28005257316582,some 24464362713336,some 21335200040700,some 18574174153080,some 16141841823510,some 14002561581840,some 12124169174520,some 10477677064400,some 9036996468045,some 7778680504140,some 6681687099710,some 5727160371180,some 4898229264825,some 4179822305984,some 3558497368608,some 3022285436352,some 2560547383576,some 2163842859360,some 1823810410032,some 1533058025824,some 1285063345176,some 1074082795968,some 895068996640,some 743595781824,some 615790256823,some 508271323092,some 418094152866,some 342700125300,some 279871768995,some 227692286640,some 184509266760,some 148902215280,some 119653565850,some 95722852680,some 76223753060,some 60403728840,some 47626016970,some 37353738800,some 29135916264,some 22595200368,some 17417133617,some 13340783196,some 10150595910,some 7669339132,some 5752004349,some 4280561376,some 3159461968,some 2311801440,some 1676056044,some 1203322288,some 854992152,some 600805296,some 417225900,some 286097760,some 193536720,some 129024480,some 84672315,some 54627300,some 34597290,some 21474180,some 13037895,some 7726160,some 4457400,some 2496144,some 1352078,some 705432,some 352716,some 167960,some 75582,some 31824,some 12376,some 4368,some 1365,some 364,some 78,some 12,some 1,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights77_identity : bernsteinWeights77=IntegerWeightedBernstein.weights 88 77 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights77_identity
def bernsteinRow77 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights77 affine01753)
theorem bernsteinRow77_weighted : bernsteinRow77=IntegerWeightedBernstein.applyWeights bernsteinWeights77 affine01753 := by decide +kernel
theorem bernsteinRow77_identity : bernsteinRow77=NestedInteger.coefficientFrom 88 77 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 77 0 affine01753 bernsteinRow77 bernsteinWeights77 bernsteinWeights77_identity bernsteinRow77_weighted
theorem bernsteinRow77_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow77=true := by decide +kernel
#print axioms bernsteinRow77_weighted
#print axioms bernsteinRow77_identity
#print axioms bernsteinRow77_positive
def bernsteinWeights78 : List (Option ℤ) := [some 4513667845896,some 4000751045226,some 3540894603246,some 3129162672636,some 2761025887620,some 2432332329570,some 2139280241670,some 1878392407320,some 1646492110120,some 1440680596355,some 1258315963905,some 1096993404430,some 954526728530,some 828931106355,some 718406958841,some 621324937376,some 536211932256,some 461738052776,some 396704524216,some 340032449328,some 290752384208,some 247994680648,some 210980549208,some 179013799328,some 151473214816,some 127805525001,some 107518933731,some 90177170226,some 75394027566,some 62828356305,some 52179482355,some 43183019880,some 35607051480,some 29248649430,some 23930713170,some 19499099620,some 15820024220,some 12777711870,some 10272278170,some 8217822536,some 6540715896,some 5178066751,some 4076350421,some 3190187286,some 2481256778,some 1917334783,some 1471442973,some 1121099408,some 847660528,some 635745396,some 472733756,some 348330136,some 254186856,some 183579396,some 131128140,some 92561040,some 64512240,some 44352165,some 30045015,some 20030010,some 13123110,some 8436285,some 5311735,some 3268760,some 1961256,some 1144066,some 646646,some 352716,some 184756,some 92378,some 43758,some 19448,some 8008,some 3003,some 1001,some 286,some 66,some 11,some 1,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights78_identity : bernsteinWeights78=IntegerWeightedBernstein.weights 88 78 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights78_identity
def bernsteinRow78 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights78 affine01753)
theorem bernsteinRow78_weighted : bernsteinRow78=IntegerWeightedBernstein.applyWeights bernsteinWeights78 affine01753 := by decide +kernel
theorem bernsteinRow78_identity : bernsteinRow78=NestedInteger.coefficientFrom 88 78 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 78 0 affine01753 bernsteinRow78 bernsteinWeights78 bernsteinWeights78_identity bernsteinRow78_weighted
theorem bernsteinRow78_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow78=true := by decide +kernel
#print axioms bernsteinRow78_weighted
#print axioms bernsteinRow78_identity
#print axioms bernsteinRow78_positive
def bernsteinWeights79 : List (Option ℤ) := [some 571350360240,some 512916800670,some 459856441980,some 411731930610,some 368136785016,some 328693558050,some 293052087900,some 260887834350,some 231900297200,some 205811513765,some 182364632450,some 161322559475,some 142466675900,some 125595622175,some 110524147514,some 97082021465,some 85113005120,some 74473879480,some 65033528560,some 56672074888,some 49280065120,some 42757703560,some 37014131440,some 31966749880,some 27540584512,some 23667689815,some 20286591270,some 17341763505,some 14783142660,some 12565671261,some 10648873950,some 8996462475,some 7575968400,some 6358402050,some 5317936260,some 4431613550,some 3679075400,some 3042312350,some 2505433700,some 2054455634,some 1677106640,some 1362649145,some 1101716330,some 886163135,some 708930508,some 563921995,some 445891810,some 350343565,some 273438880,some 211915132,some 163011640,some 124403620,some 94143280,some 70607460,some 52451256,some 38567100,some 28048800,some 20160075,some 14307150,some 10015005,some 6906900,some 4686825,some 3124550,some 2042975,some 1307504,some 817190,some 497420,some 293930,some 167960,some 92378,some 48620,some 24310,some 11440,some 5005,some 2002,some 715,some 220,some 55,some 10,some 1,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights79_identity : bernsteinWeights79=IntegerWeightedBernstein.weights 88 79 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights79_identity
def bernsteinRow79 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights79 affine01753)
theorem bernsteinRow79_weighted : bernsteinRow79=IntegerWeightedBernstein.applyWeights bernsteinWeights79 affine01753 := by decide +kernel
theorem bernsteinRow79_identity : bernsteinRow79=NestedInteger.coefficientFrom 88 79 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 79 0 affine01753 bernsteinRow79 bernsteinWeights79 bernsteinWeights79_identity bernsteinRow79_weighted
theorem bernsteinRow79_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow79=true := by decide +kernel
#print axioms bernsteinRow79_weighted
#print axioms bernsteinRow79_identity
#print axioms bernsteinRow79_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
