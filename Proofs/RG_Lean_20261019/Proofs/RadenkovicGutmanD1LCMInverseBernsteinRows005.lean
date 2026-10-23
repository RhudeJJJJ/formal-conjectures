/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinWeights25 : List (Option ℤ) := [some 6031435276240042413888,some 1713475930750012049400,some 472683015379313668800,some 126415225043304818400,some 32719234717090658880,some 8179808679272664720,some 1971038235969316800,some 456703981505085600,some 101489773667796800,some 21566576904406820,some 4367914309753280,some 839983521106400,some 152724276564800,some 26123889412400,some 4179822305984,some 621324937376,some 85113005120,some 10639125640,some 1198774720,some 119877472,some 10424128,some 766480,some 45760,some 2080,some 64,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights25_identity : bernsteinWeights25=IntegerWeightedBernstein.weights 88 25 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights25_identity
def bernsteinRow25 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights25 affine01753)
theorem bernsteinRow25_weighted : bernsteinRow25=IntegerWeightedBernstein.applyWeights bernsteinWeights25 affine01753 := by decide +kernel
theorem bernsteinRow25_identity : bernsteinRow25=NestedInteger.coefficientFrom 88 25 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 25 0 affine01753 bernsteinRow25 bernsteinWeights25 bernsteinWeights25_identity bernsteinRow25_weighted
theorem bernsteinRow25_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow25=true := by decide +kernel
#print axioms bernsteinRow25_weighted
#print axioms bernsteinRow25_identity
#print axioms bernsteinRow25_positive
def bernsteinWeights26 : List (Option ℤ) := [some 14614631630889333541344,some 4317959345490030364488,some 1240792915370698380600,some 346267790336008850400,some 93695990326214159520,some 24539426037817994160,some 6208770443303347920,some 1514334254464231200,some 355214207837288800,some 79923196763389980,some 17198662594653540,some 3527930788646880,some 687259244541600,some 126600387152400,some 21944067106416,some 3558497368608,some 536211932256,some 74473879480,some 9440350920,some 1078897248,some 109453344,some 9657648,some 720720,some 43680,some 2016,some 63,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights26_identity : bernsteinWeights26=IntegerWeightedBernstein.weights 88 26 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights26_identity
def bernsteinRow26 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights26 affine01753)
theorem bernsteinRow26_weighted : bernsteinRow26=IntegerWeightedBernstein.applyWeights bernsteinWeights26 affine01753 := by decide +kernel
theorem bernsteinRow26_identity : bernsteinRow26=NestedInteger.coefficientFrom 88 26 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 26 0 affine01753 bernsteinRow26 bernsteinWeights26 bernsteinWeights26_identity bernsteinRow26_weighted
theorem bernsteinRow26_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow26=true := by decide +kernel
#print axioms bernsteinRow26_weighted
#print axioms bernsteinRow26_identity
#print axioms bernsteinRow26_positive
def bernsteinWeights27 : List (Option ℤ) := [some 33559524485745877020864,some 10296672285399303176856,some 3077166430119331983888,some 894525125034689530200,some 252571800009794690880,some 69156564288396165360,some 18330655594514646240,some 4694436188839116720,some 1159120046626942400,some 275291011073898820,some 62724534168736440,some 13670731806006660,some 2840671544105280,some 560658857389200,some 104656320045984,some 18385569737808,some 3022285436352,some 461738052776,some 65033528560,some 8361453672,some 969443904,some 99795696,some 8936928,some 677040,some 41664,some 1953,some 62,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights27_identity : bernsteinWeights27=IntegerWeightedBernstein.weights 88 27 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights27_identity
def bernsteinRow27 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights27 affine01753)
theorem bernsteinRow27_weighted : bernsteinRow27=IntegerWeightedBernstein.applyWeights bernsteinWeights27 affine01753 := by decide +kernel
theorem bernsteinRow27_identity : bernsteinRow27=NestedInteger.coefficientFrom 88 27 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 27 0 affine01753 bernsteinRow27 bernsteinWeights27 bernsteinWeights27_identity bernsteinRow27_weighted
theorem bernsteinRow27_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow27=true := by decide +kernel
#print axioms bernsteinRow27_weighted
#print axioms bernsteinRow27_identity
#print axioms bernsteinRow27_positive
def bernsteinWeights28 : List (Option ℤ) := [some 73111821201089232081168,some 23262852200346573844008,some 7219505855279971192968,some 2182641305084642453688,some 641953325024894839320,some 183415235721398525520,some 50825908693881519120,some 13636219405675529520,some 3535316142212174320,some 883829035553043580,some 212566476905162380,some 49053802362729780,some 10830060261901380,some 2280012686716080,some 456002537343216,some 86270750308176,some 15363284301456,some 2560547383576,some 396704524216,some 56672074888,some 7392009768,some 869648208,some 90858768,some 8259888,some 635376,some 39711,some 1891,some 61,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights28_identity : bernsteinWeights28=IntegerWeightedBernstein.weights 88 28 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights28_identity
def bernsteinRow28 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights28 affine01753)
theorem bernsteinRow28_weighted : bernsteinRow28=IntegerWeightedBernstein.applyWeights bernsteinWeights28 affine01753 := by decide +kernel
theorem bernsteinRow28_identity : bernsteinRow28=NestedInteger.coefficientFrom 88 28 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 28 0 affine01753 bernsteinRow28 bernsteinWeights28 bernsteinWeights28_identity bernsteinRow28_weighted
theorem bernsteinRow28_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow28=true := by decide +kernel
#print axioms bernsteinRow28_weighted
#print axioms bernsteinRow28_identity
#print axioms bernsteinRow28_positive
def bernsteinWeights29 : List (Option ℤ) := [some 151265836967770824995520,some 49848969000742658237160,some 16043346345066602651040,some 5036864550195328739280,some 1540687980059747614368,some 458538089303496313800,some 132589327027517006400,some 37189689288205989600,some 10100903263463355200,some 2651487106659130740,some 671262558647881200,some 163512674542432600,some 38223742100828400,some 8550047575185300,some 1824010149372864,some 369731787035040,some 70907466006720,some 12802736917880,some 2163842859360,some 340032449328,some 49280065120,some 6522361560,some 778789440,some 82598880,some 7624512,some 595665,some 37820,some 1830,some 60,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights29_identity : bernsteinWeights29=IntegerWeightedBernstein.weights 88 29 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights29_identity
def bernsteinRow29 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights29 affine01753)
theorem bernsteinRow29_weighted : bernsteinRow29=IntegerWeightedBernstein.applyWeights bernsteinWeights29 affine01753 := by decide +kernel
theorem bernsteinRow29_identity : bernsteinRow29=NestedInteger.coefficientFrom 88 29 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 29 0 affine01753 bernsteinRow29 bernsteinWeights29 bernsteinWeights29_identity bernsteinRow29_weighted
theorem bernsteinRow29_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow29=true := by decide +kernel
#print axioms bernsteinRow29_weighted
#print axioms bernsteinRow29_identity
#print axioms bernsteinRow29_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
