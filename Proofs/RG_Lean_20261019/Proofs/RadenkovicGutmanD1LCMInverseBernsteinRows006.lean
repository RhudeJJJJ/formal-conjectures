/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinWeights30 : List (Option ℤ) := [some 297489479369949289157856,some 101416867967028166758360,some 33805622655676055586120,some 11006481794871273911760,some 3496176570135581124912,some 1082149890756251300568,some 325948762275979307400,some 95399637739311016800,some 27088786024742634400,some 7449416156804224460,some 1980224548011249540,some 507749884105448600,some 125288932441604200,some 29673694525643100,some 6726037425812436,some 1454278362337824,some 298824321028320,some 58104729088840,some 10638894058520,some 1823810410032,some 290752384208,some 42757703560,some 5743572120,some 696190560,some 74974368,some 7028847,some 557845,some 35990,some 1770,some 59,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights30_identity : bernsteinWeights30=IntegerWeightedBernstein.weights 88 30 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights30_identity
def bernsteinRow30 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights30 affine01753)
theorem bernsteinRow30_weighted : bernsteinRow30=IntegerWeightedBernstein.applyWeights bernsteinWeights30 affine01753 := by decide +kernel
theorem bernsteinRow30_identity : bernsteinRow30=NestedInteger.coefficientFrom 88 30 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 30 0 affine01753 bernsteinRow30 bernsteinWeights30 bernsteinWeights30_identity bernsteinRow30_weighted
theorem bernsteinRow30_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow30=true := by decide +kernel
#print axioms bernsteinRow30_weighted
#print axioms bernsteinRow30_identity
#print axioms bernsteinRow30_positive
def bernsteinWeights31 : List (Option ℤ) := [some 556593219466356734553408,some 196072611402921122399496,some 67611245311352111172240,some 22799140860804781674360,some 7510305224735692786848,some 2414026679379329824344,some 756201128480271993168,some 230549124536668290600,some 68310851714568382400,some 19639369867938409940,some 5469191608792974920,some 1472474663905800940,some 382460951663844400,some 95615237915961100,some 22947657099830664,some 5271759063474612,some 1155454041309504,some 240719591939480,some 47465835030320,some 8815083648488,some 1533058025824,some 247994680648,some 37014131440,some 5047381560,some 621216192,some 67945521,some 6471002,some 521855,some 34220,some 1711,some 58,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights31_identity : bernsteinWeights31=IntegerWeightedBernstein.weights 88 31 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights31_identity
def bernsteinRow31 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights31 affine01753)
theorem bernsteinRow31_weighted : bernsteinRow31=IntegerWeightedBernstein.applyWeights bernsteinWeights31 affine01753 := by decide +kernel
theorem bernsteinRow31_identity : bernsteinRow31=NestedInteger.coefficientFrom 88 31 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 31 0 affine01753 bernsteinRow31 bernsteinWeights31 bernsteinWeights31_identity bernsteinRow31_weighted
theorem bernsteinRow31_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow31=true := by decide +kernel
#print axioms bernsteinRow31_weighted
#print axioms bernsteinRow31_identity
#print axioms bernsteinRow31_positive
def bernsteinWeights32 : List (Option ℤ) := [some 991431672174447933423258,some 360520608063435612153912,some 128461366091569011227256,some 44812104450547329497880,some 15288835636069088887512,some 5096278545356362962504,some 1657825550899057831176,some 525652003943603702568,some 162238272822099908200,some 48671481846629972460,some 14170178259145435020,some 3996716944887173980,some 1090013712241956540,some 286845713747883300,some 72667580816130436,some 17675898036356052,some 4116305022165108,some 914734449370024,some 193253756909160,some 38650751381832,some 7282025622664,some 1285063345176,some 210980549208,some 31966749880,some 4426165368,some 553270671,some 61474519,some 5949147,some 487635,some 32509,some 1653,some 57,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights32_identity : bernsteinWeights32=IntegerWeightedBernstein.weights 88 32 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights32_identity
def bernsteinRow32 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights32 affine01753)
theorem bernsteinRow32_weighted : bernsteinRow32=IntegerWeightedBernstein.applyWeights bernsteinWeights32 affine01753 := by decide +kernel
theorem bernsteinRow32_identity : bernsteinRow32=NestedInteger.coefficientFrom 88 32 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 32 0 affine01753 bernsteinRow32 bernsteinWeights32 bernsteinWeights32_identity bernsteinRow32_weighted
theorem bernsteinRow32_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow32=true := by decide +kernel
#print axioms bernsteinRow32_weighted
#print axioms bernsteinRow32_identity
#print axioms bernsteinRow32_positive
def bernsteinWeights33 : List (Option ℤ) := [some 1682429504296032856718256,some 630911064111012321269346,some 232059241971866600926656,some 83649261641021681729376,some 29523268814478240610368,some 10192557090712725925008,some 3438452994457305131328,some 1132173546955454128608,some 363413731121503794368,some 113566790975469935740,some 34501303587484537440,some 10173461314258261040,some 2906703232645217440,some 803167998494073240,some 214178132931752864,some 54991682779774384,some 13559593014190944,some 3201570572795084,some 721480692460864,some 154603005527328,some 31368725759168,some 5996962277488,some 1074082795968,some 179013799328,some 27540584512,some 3872894697,some 491796152,some 55525372,some 5461512,some 455126,some 30856,some 1596,some 56,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights33_identity : bernsteinWeights33=IntegerWeightedBernstein.weights 88 33 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights33_identity
def bernsteinRow33 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights33 affine01753)
theorem bernsteinRow33_weighted : bernsteinRow33=IntegerWeightedBernstein.applyWeights bernsteinWeights33 affine01753 := by decide +kernel
theorem bernsteinRow33_identity : bernsteinRow33=NestedInteger.coefficientFrom 88 33 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 33 0 affine01753 bernsteinRow33 bernsteinWeights33 bernsteinWeights33_identity bernsteinRow33_weighted
theorem bernsteinRow33_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow33=true := by decide +kernel
#print axioms bernsteinRow33_weighted
#print axioms bernsteinRow33_identity
#print axioms bernsteinRow33_positive
def bernsteinWeights34 : List (Option ℤ) := [some 2721577139302406091750120,some 1051518440185020535448910,some 398851822139145720342690,some 148409980330844919197280,some 54125992826543441119008,some 19330711723765514685360,some 6754104096255420793680,some 2306279447501851002720,some 768759815833950334240,some 249846940146033858628,some 79065487387985398300,some 24327842273226276400,some 7266758081613043600,some 2103535234151144200,some 588989865562320376,some 159186450151978480,some 41432089765583440,some 10358022441395860,some 2480089880334220,some 566877686933536,some 123234279768160,some 25371763481680,some 4922879481520,some 895068996640,some 151473214816,some 23667689815,some 3381098545,some 436270780,some 50063860,some 5006386,some 424270,some 29260,some 1540,some 55,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights34_identity : bernsteinWeights34=IntegerWeightedBernstein.weights 88 34 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights34_identity
def bernsteinRow34 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights34 affine01753)
theorem bernsteinRow34_weighted : bernsteinRow34=IntegerWeightedBernstein.applyWeights bernsteinWeights34 affine01753 := by decide +kernel
theorem bernsteinRow34_identity : bernsteinRow34=NestedInteger.coefficientFrom 88 34 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 34 0 affine01753 bernsteinRow34 bernsteinWeights34 bernsteinWeights34_identity bernsteinRow34_weighted
theorem bernsteinRow34_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow34=true := by decide +kernel
#print axioms bernsteinRow34_weighted
#print axioms bernsteinRow34_identity
#print axioms bernsteinRow34_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
