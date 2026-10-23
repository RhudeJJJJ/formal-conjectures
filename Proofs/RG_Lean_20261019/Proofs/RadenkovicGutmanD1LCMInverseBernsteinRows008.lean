/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinWeights40 : List (Option ℤ) := [some 18312575054317505569702710,some 8323897751962502531683050,some 3731402440534914927995850,some 1648759217910776363533050,some 717695188972926181773210,some 307583652416968363617090,some 129703949814384249718050,some 53779686508403225492850,some 21910242651571684460050,some 8764097060628673784020,some 3439076061765682117780,some 1322721562217570045300,some 498167861094928978100,some 183535527771815939300,some 66072789997853738148,some 23214764053299962052,some 7950261662089028100,some 2650087220696342700,some 858478958817125100,some 269807672771096460,some 82115378669464140,some 24151581961607100,some 6848956078664700,some 1867897112363100,some 488526937079580,some 122131734269895,some 29078984349975,some 6566222272575,some 1399358844975,some 279871768995,some 52179482355,some 8996462475,some 1420494075,some 202927725,some 25827165,some 2869685,some 270725,some 20825,some 1225,some 49,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights40_identity : bernsteinWeights40=IntegerWeightedBernstein.weights 88 40 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights40_identity
def bernsteinRow40 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights40 affine01753)
theorem bernsteinRow40_weighted : bernsteinRow40=IntegerWeightedBernstein.applyWeights bernsteinWeights40 affine01753 := by decide +kernel
theorem bernsteinRow40_identity : bernsteinRow40=NestedInteger.coefficientFrom 88 40 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 40 0 affine01753 bernsteinRow40 bernsteinWeights40 bernsteinWeights40_identity bernsteinRow40_weighted
theorem bernsteinRow40_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow40=true := by decide +kernel
#print axioms bernsteinRow40_weighted
#print axioms bernsteinRow40_identity
#print axioms bernsteinRow40_positive
def bernsteinWeights41 : List (Option ℤ) := [some 21439112258713177252334880,some 9988677302355003038019660,some 4592495311427587603687200,some 2082643222624138564462800,some 931064028937850181759840,some 410111536555957818156120,some 177879702602584113899040,some 75924263305981024225200,some 31869443856831541032800,some 13146145590943010676030,some 5325020998862991666240,some 2116354499548112072480,some 824553701122641067200,some 314632333323113038800,some 117462737773962201152,some 42858025944553776096,some 15264502391210933952,some 5300174441392685400,some 1791608261879217600,some 588671286046028640,some 187692294101632320,some 57963796707857040,some 17302625882942400,some 4981058966301600,some 1379370175283520,some 366395202809685,some 93052749919920,some 22512762077400,some 5166863427600,some 1119487075980,some 227692286640,some 43183019880,some 7575968400,some 1217566350,some 177100560,some 22957480,some 2598960,some 249900,some 19600,some 1176,some 48,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights41_identity : bernsteinWeights41=IntegerWeightedBernstein.weights 88 41 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights41_identity
def bernsteinRow41 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights41 affine01753)
theorem bernsteinRow41_weighted : bernsteinRow41=IntegerWeightedBernstein.applyWeights bernsteinWeights41 affine01753 := by decide +kernel
theorem bernsteinRow41_identity : bernsteinRow41=NestedInteger.coefficientFrom 88 41 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 41 0 affine01753 bernsteinRow41 bernsteinWeights41 bernsteinWeights41_identity bernsteinRow41_weighted
theorem bernsteinRow41_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow41=true := by decide +kernel
#print axioms bernsteinRow41_weighted
#print axioms bernsteinRow41_identity
#print axioms bernsteinRow41_positive
def bernsteinWeights42 : List (Option ℤ) := [some 23991387527607603115708080,some 11450434956358174214315220,some 5396181990927415434332460,some 2509852088803449039224400,some 1151579193686288382702960,some 520952492381892363603720,some 232231833953373704257080,some 101955439296603089673840,some 44054819449149483192400,some 18723298265888530356770,some 7821124592080019009790,some 3208666499314879593760,some 1291800798425471005280,some 509921367799528028400,some 197169595549150837648,some 74604711829408425056,some 27593523553342842144,some 9964327949818248552,some 3508566179513467800,some 1202936975833188960,some 400978991944396320,some 129728497393775280,some 40661170824914640,some 12321566916640800,some 3601688791018080,some 1012974972473835,some 273342452889765,some 70539987842520,some 17345898649800,some 4047376351620,some 891794789340,some 184509266760,some 35607051480,some 6358402050,some 1040465790,some 154143080,some 20358520,some 2349060,some 230300,some 18424,some 1128,some 47,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights42_identity : bernsteinWeights42=IntegerWeightedBernstein.weights 88 42 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights42_identity
def bernsteinRow42 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights42 affine01753)
theorem bernsteinRow42_weighted : bernsteinRow42=IntegerWeightedBernstein.applyWeights bernsteinWeights42 affine01753 := by decide +kernel
theorem bernsteinRow42_identity : bernsteinRow42=NestedInteger.coefficientFrom 88 42 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 42 0 affine01753 bernsteinRow42 bernsteinWeights42 bernsteinWeights42_identity bernsteinRow42_weighted
theorem bernsteinRow42_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow42=true := by decide +kernel
#print axioms bernsteinRow42_weighted
#print axioms bernsteinRow42_identity
#print axioms bernsteinRow42_positive
def bernsteinWeights43 : List (Option ℤ) := [some 25665205262091854495873760,some 12540952571249428901392860,some 6054252965430758779982760,some 2886329902123966395108060,some 1358272895117160656521440,some 630626701304396019099240,some 288720658428518659346640,some 130276394656770614583240,some 57900619847453606481440,some 25331521183260952835630,some 10902173673808511346980,some 4612458092765139416030,some 1916865700889408588480,some 781879430625942976880,some 312751772250377190752,some 122564883719742412592,some 47011188276065582912,some 17629195603524593592,some 6455761770304780752,some 2305629203680278840,some 801957983888792640,some 271250494550621040,some 89067326568860640,some 28339603908273840,some 8719878125622720,some 2588713818544245,some 739632519584070,some 202802465047245,some 53194089192720,some 13298522298180,some 3155581562280,some 707285522580,some 148902215280,some 29248649430,some 5317936260,some 886322710,some 133784560,some 18009460,some 2118760,some 211876,some 17296,some 1081,some 46,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights43_identity : bernsteinWeights43=IntegerWeightedBernstein.weights 88 43 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights43_identity
def bernsteinRow43 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights43 affine01753)
theorem bernsteinRow43_weighted : bernsteinRow43=IntegerWeightedBernstein.applyWeights bernsteinWeights43 affine01753 := by decide +kernel
theorem bernsteinRow43_identity : bernsteinRow43=NestedInteger.coefficientFrom 88 43 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 43 0 affine01753 bernsteinRow43 bernsteinWeights43 bernsteinWeights43_identity bernsteinRow43_weighted
theorem bernsteinRow43_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow43=true := by decide +kernel
#print axioms bernsteinRow43_weighted
#print axioms bernsteinRow43_identity
#print axioms bernsteinRow43_positive
def bernsteinWeights44 : List (Option ℤ) := [some 26248505381684851188961800,some 13124252690842425594480900,some 6486699605818670121410100,some 3167923063306792384874700,some 1528057007006805738586620,some 727646193812764637422200,some 341906042875877359752600,some 158444263771748044763400,some 72375774809317008101800,some 32569098664192653645810,some 14429347509452441488650,some 6289715581043371930950,some 2695592391875730827550,some 1134986270263465611600,some 469127658375565786128,some 190186888530634778160,some 75553695443676829680,some 29381992672540989320,some 11173433833219812840,some 4150132566624501912,some 1503671219791486200,some 530707489338171600,some 182183167981760400,some 60727722660586800,some 19619725782651120,some 6131164307078475,some 1849081298960175,some 536830054536825,some 149608375854525,some 39895566894540,some 10142940735900,some 2448296039700,some 558383307300,some 119653565850,some 23930713170,some 4431613550,some 752538150,some 115775100,some 15890700,some 1906884,some 194580,some 16215,some 1035,some 45,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights44_identity : bernsteinWeights44=IntegerWeightedBernstein.weights 88 44 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights44_identity
def bernsteinRow44 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights44 affine01753)
theorem bernsteinRow44_weighted : bernsteinRow44=IntegerWeightedBernstein.applyWeights bernsteinWeights44 affine01753 := by decide +kernel
theorem bernsteinRow44_identity : bernsteinRow44=NestedInteger.coefficientFrom 88 44 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 44 0 affine01753 bernsteinRow44 bernsteinWeights44 bernsteinWeights44_identity bernsteinRow44_weighted
theorem bernsteinRow44_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow44=true := by decide +kernel
#print axioms bernsteinRow44_weighted
#print axioms bernsteinRow44_identity
#print axioms bernsteinRow44_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
