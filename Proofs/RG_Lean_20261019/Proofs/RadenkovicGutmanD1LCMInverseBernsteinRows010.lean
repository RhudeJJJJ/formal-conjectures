/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinWeights50 : List (Option ℤ) := [some 11660251871320534158667848,some 6625143108704848953788550,some 3731402440534914927995850,some 2082643222624138564462800,some 1151579193686288382702960,some 630626701304396019099240,some 341906042875877359752600,some 183461779104129314989200,some 97393290141698278327600,some 51131477324391596121990,some 26536589497469056215210,some 13608507434599516007800,some 6892620648693261354600,some 3446310324346630677300,some 1700179760011004467468,some 827114477843191362552,some 396561735952215036840,some 187265264199657100730,some 87038784768854708790,some 39789158751476438304,some 17876288714431443296,some 7886597962249166160,some 3413602103063071920,some 1448194831602515360,some 601557853127198688,some 244382877832924467,some 96977332473382725,some 37539612570341700,some 14154280149473100,some 5189902721473470,some 1847253511032930,some 636983969321700,some 212327989773900,some 68248282427325,some 21094923659355,some 6250347750920,some 1768966344600,some 476260169700,some 121399651100,some 29135916264,some 6540715896,some 1362649145,some 260932815,some 45379620,some 7059052,some 962598,some 111930,some 10660,some 780,some 39,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights50_identity : bernsteinWeights50=IntegerWeightedBernstein.weights 88 50 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights50_identity
def bernsteinRow50 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights50 affine01753)
theorem bernsteinRow50_weighted : bernsteinRow50=IntegerWeightedBernstein.applyWeights bernsteinWeights50 affine01753 := by decide +kernel
theorem bernsteinRow50_identity : bernsteinRow50=NestedInteger.coefficientFrom 88 50 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 50 0 affine01753 bernsteinRow50 bernsteinWeights50 bernsteinWeights50_identity bernsteinRow50_weighted
theorem bernsteinRow50_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow50=true := by decide +kernel
#print axioms bernsteinRow50_weighted
#print axioms bernsteinRow50_identity
#print axioms bernsteinRow50_positive
def bernsteinWeights51 : List (Option ℤ) := [some 8688030806081966628027024,some 5035108762615685204879298,some 2893740668169934025792700,some 1648759217910776363533050,some 931064028937850181759840,some 520952492381892363603720,some 288720658428518659346640,some 158444263771748044763400,some 86068488962431036661600,some 46261812817306682205610,some 24594887826922539906780,some 12928082062869540207410,some 6715886785906254653200,some 3446310324346630677300,some 1746130564335626209832,some 873065282167813104916,some 430552741890976325712,some 209296471752557936110,some 100226479430802391940,some 47249626017378270486,some 21912870037044995008,some 9989690752182277136,some 4472995859186094240,some 1965407271460556560,some 846636978475316672,some 357174975294274221,some 147405545359541742,some 59437719903041025,some 23385332420868600,some 8964377427999630,some 3342649210440540,some 1210269541711230,some 424655979547800,some 144079707346575,some 47153358767970,some 14844575908435,some 4481381406320,some 1292706174900,some 354860518600,some 92263734836,some 22595200368,some 5178066751,some 1101716330,some 215553195,some 38320568,some 6096454,some 850668,some 101270,some 9880,some 741,some 38,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights51_identity : bernsteinWeights51=IntegerWeightedBernstein.weights 88 51 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights51_identity
def bernsteinRow51 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights51 affine01753)
theorem bernsteinRow51_weighted : bernsteinRow51=IntegerWeightedBernstein.applyWeights bernsteinWeights51 affine01753 := by decide +kernel
theorem bernsteinRow51_identity : bernsteinRow51=NestedInteger.coefficientFrom 88 51 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 51 0 affine01753 bernsteinRow51 bernsteinWeights51 bernsteinWeights51_identity bernsteinRow51_weighted
theorem bernsteinRow51_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow51=true := by decide +kernel
#print axioms bernsteinRow51_weighted
#print axioms bernsteinRow51_identity
#print axioms bernsteinRow51_positive
def bernsteinWeights52 : List (Option ℤ) := [some 6181868073558322408403844,some 3652922043466281423147726,some 2141368094445751179086598,some 1244981450259157662259650,some 717695188972926181773210,some 410111536555957818156120,some 232231833953373704257080,some 130276394656770614583240,some 72375774809317008101800,some 39806676145124354455990,some 21666924990384142298830,some 11666805764052999699370,some 6212195276963285554210,some 3269576461559623975900,some 1700179760011004467468,some 873065282167813104916,some 442512540276836779204,some 221256270138418389602,some 109069992321755544170,some 52976853413424121454,some 25336755980333275478,some 11923179284862717872,some 5516694892996182896,some 2507588587725537680,some 1118770292985239888,some 489462003181042451,some 209769429934732479,some 87967825456500717,some 36052387482172425,some 14420954992868970,some 5621728217559090,some 2132379668729310,some 785613562163430,some 280576272201225,some 96926348578605,some 32308782859535,some 10363194502115,some 3188675231420,some 937845656300,some 262596783764,some 69668534468,some 17417133617,some 4076350421,some 886163135,some 177232627,some 32224114,some 5245786,some 749398,some 91390,some 9139,some 703,some 37,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights52_identity : bernsteinWeights52=IntegerWeightedBernstein.weights 88 52 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights52_identity
def bernsteinRow52 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights52 affine01753)
theorem bernsteinRow52_weighted : bernsteinRow52=IntegerWeightedBernstein.applyWeights bernsteinWeights52 affine01753 := by decide +kernel
theorem bernsteinRow52_identity : bernsteinRow52=NestedInteger.coefficientFrom 88 52 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 52 0 affine01753 bernsteinRow52 bernsteinWeights52 bernsteinWeights52_identity bernsteinRow52_weighted
theorem bernsteinRow52_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow52=true := by decide +kernel
#print axioms bernsteinRow52_weighted
#print axioms bernsteinRow52_identity
#print axioms bernsteinRow52_positive
def bernsteinWeights53 : List (Option ℤ) := [some 4199004729209426541557328,some 2528946030092040985256118,some 1511553949020530244061128,some 896386644186593516826948,some 527286261286231480486440,some 307583652416968363617090,some 177879702602584113899040,some 101955439296603089673840,some 57900619847453606481440,some 32569098664192653645810,some 18139751154740212157160,some 10000119226331142599460,some 5454610487089714145160,some 2942618815403661578310,some 1569396701548619508432,some 827114477843191362552,some 430552741890976325712,some 221256270138418389602,some 112186277816662845432,some 56093138908331422716,some 27640097433090845976,some 13413576695470557606,some 6406484391866534976,some 3009106305270645216,some 1388818294740297792,some 629308289804197437,some 279692573246309972,some 121801604478231762,some 51915437974328292,some 21631432489303455,some 8799226775309880,some 3489348548829780,some 1346766106565880,some 505037289962205,some 183649923622620,some 64617565719070,some 21945588357420,some 7174519270695,some 2250829575120,some 675248872536,some 192928249296,some 52251400851,some 13340783196,some 3190187286,some 708930508,some 145008513,some 26978328,some 4496388,some 658008,some 82251,some 8436,some 666,some 36,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights53_identity : bernsteinWeights53=IntegerWeightedBernstein.weights 88 53 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights53_identity
def bernsteinRow53 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights53 affine01753)
theorem bernsteinRow53_weighted : bernsteinRow53=IntegerWeightedBernstein.applyWeights bernsteinWeights53 affine01753 := by decide +kernel
theorem bernsteinRow53_identity : bernsteinRow53=NestedInteger.coefficientFrom 88 53 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 53 0 affine01753 bernsteinRow53 bernsteinWeights53 bernsteinWeights53_identity bernsteinRow53_weighted
theorem bernsteinRow53_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow53=true := by decide +kernel
#print axioms bernsteinRow53_weighted
#print axioms bernsteinRow53_identity
#print axioms bernsteinRow53_positive
def bernsteinWeights54 : List (Option ℤ) := [some 2721577139302406091750120,some 1670058699117385556301210,some 1017392081071510741194990,some 615167304833936727234180,some 369100382900362036340508,some 219702608869263116869350,some 129703949814384249718050,some 75924263305981024225200,some 44054819449149483192400,some 25331521183260952835630,some 14429347509452441488650,some 8139631928409069557700,some 4545508739241428454300,some 2511991671686052566850,some 1373222113855042069878,some 742282223705428145880,some 396561735952215036840,some 209296471752557936110,some 109069992321755544170,some 56093138908331422716,some 28453041475240576740,some 14226520737620288370,some 7007092303604022630,some 3397378086595889760,some 1620288010530347424,some 759510004936100355,some 349615716557887465,some 157890968768078210,some 69886166503903470,some 30284005485024837,some 12832205713993575,some 5309878226480100,some 2142582442263900,some 841728816603675,some 321387366339585,some 119032357903550,some 42671977361650,some 14771069086725,some 4923689695575,some 1575580702584,some 482320623240,some 140676848445,some 38910617655,some 10150595910,some 2481256778,some 563921995,some 118030185,some 22481940,some 3838380,some 575757,some 73815,some 7770,some 630,some 35,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights54_identity : bernsteinWeights54=IntegerWeightedBernstein.weights 88 54 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights54_identity
def bernsteinRow54 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights54 affine01753)
theorem bernsteinRow54_weighted : bernsteinRow54=IntegerWeightedBernstein.applyWeights bernsteinWeights54 affine01753 := by decide +kernel
theorem bernsteinRow54_identity : bernsteinRow54=NestedInteger.coefficientFrom 88 54 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 54 0 affine01753 bernsteinRow54 bernsteinWeights54 bernsteinWeights54_identity bernsteinRow54_weighted
theorem bernsteinRow54_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow54=true := by decide +kernel
#print axioms bernsteinRow54_weighted
#print axioms bernsteinRow54_identity
#print axioms bernsteinRow54_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
