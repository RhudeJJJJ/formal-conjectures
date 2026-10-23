/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinWeights80 : List (Option ℤ) := [some 64276915527,some 58433559570,some 53060358690,some 48124511370,some 43595145594,some 39443226966,some 35641470150,some 32164253550,some 28987537150,some 26088783435,some 23446881315,some 21042072975,some 18855883575,some 16871053725,some 15071474661,some 13442126049,some 11969016345,some 10639125640,some 9440350920,some 8361453672,some 7392009768,some 6522361560,some 5743572120,some 5047381560,some 4426165368,some 3872894697,some 3381098545,some 2944827765,some 2558620845,some 2217471399,some 1916797311,some 1652411475,some 1420494075,some 1217566350,some 1040465790,some 886322710,some 752538150,some 636763050,some 536878650,some 450978066,some 377348994,some 314457495,some 260932815,some 215553195,some 177232627,some 145008513,some 118030185,some 95548245,some 76904685,some 61523748,some 48903492,some 38608020,some 30260340,some 23535820,some 18156204,some 13884156,some 10518300,some 7888725,some 5852925,some 4292145,some 3108105,some 2220075,some 1562275,some 1081575,some 735471,some 490314,some 319770,some 203490,some 125970,some 75582,some 43758,some 24310,some 12870,some 6435,some 3003,some 1287,some 495,some 165,some 45,some 9,some 1,none,none,none,none,none,none,none,none]
theorem bernsteinWeights80_identity : bernsteinWeights80=IntegerWeightedBernstein.weights 88 80 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights80_identity
def bernsteinRow80 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights80 affine01753)
theorem bernsteinRow80_weighted : bernsteinRow80=IntegerWeightedBernstein.applyWeights bernsteinWeights80 affine01753 := by decide +kernel
theorem bernsteinRow80_identity : bernsteinRow80=NestedInteger.coefficientFrom 88 80 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 80 0 affine01753 bernsteinRow80 bernsteinWeights80 bernsteinWeights80_identity bernsteinRow80_weighted
theorem bernsteinRow80_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow80=true := by decide +kernel
#print axioms bernsteinRow80_weighted
#print axioms bernsteinRow80_identity
#print axioms bernsteinRow80_positive
def bernsteinWeights81 : List (Option ℤ) := [some 6348337336,some 5843355957,some 5373200880,some 4935847320,some 4529365776,some 4151918628,some 3801756816,some 3477216600,some 3176716400,some 2898753715,some 2641902120,some 2404808340,some 2186189400,some 1984829850,some 1799579064,some 1629348612,some 1473109704,some 1329890705,some 1198774720,some 1078897248,some 969443904,some 869648208,some 778789440,some 696190560,some 621216192,some 553270671,some 491796152,some 436270780,some 386206920,some 341149446,some 300674088,some 264385836,some 231917400,some 202927725,some 177100560,some 154143080,some 133784560,some 115775100,some 99884400,some 85900584,some 73629072,some 62891499,some 53524680,some 45379620,some 38320568,some 32224114,some 26978328,some 22481940,some 18643560,some 15380937,some 12620256,some 10295472,some 8347680,some 6724520,some 5379616,some 4272048,some 3365856,some 2629575,some 2035800,some 1560780,some 1184040,some 888030,some 657800,some 480700,some 346104,some 245157,some 170544,some 116280,some 77520,some 50388,some 31824,some 19448,some 11440,some 6435,some 3432,some 1716,some 792,some 330,some 120,some 36,some 8,some 1,none,none,none,none,none,none,none]
theorem bernsteinWeights81_identity : bernsteinWeights81=IntegerWeightedBernstein.weights 88 81 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights81_identity
def bernsteinRow81 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights81 affine01753)
theorem bernsteinRow81_weighted : bernsteinRow81=IntegerWeightedBernstein.applyWeights bernsteinWeights81 affine01753 := by decide +kernel
theorem bernsteinRow81_identity : bernsteinRow81=NestedInteger.coefficientFrom 88 81 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 81 0 affine01753 bernsteinRow81 bernsteinWeights81 bernsteinWeights81_identity bernsteinRow81_weighted
theorem bernsteinRow81_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow81=true := by decide +kernel
#print axioms bernsteinRow81_weighted
#print axioms bernsteinRow81_identity
#print axioms bernsteinRow81_positive
def bernsteinWeights82 : List (Option ℤ) := [some 541931236,some 504981379,some 470155077,some 437353560,some 406481544,some 377447148,some 350161812,some 324540216,some 300500200,some 277962685,some 256851595,some 237093780,some 218618940,some 201359550,some 185250786,some 170230452,some 156238908,some 143218999,some 131115985,some 119877472,some 109453344,some 99795696,some 90858768,some 82598880,some 74974368,some 67945521,some 61474519,some 55525372,some 50063860,some 45057474,some 40475358,some 36288252,some 32468436,some 28989675,some 25827165,some 22957480,some 20358520,some 18009460,some 15890700,some 13983816,some 12271512,some 10737573,some 9366819,some 8145060,some 7059052,some 6096454,some 5245786,some 4496388,some 3838380,some 3262623,some 2760681,some 2324784,some 1947792,some 1623160,some 1344904,some 1107568,some 906192,some 736281,some 593775,some 475020,some 376740,some 296010,some 230230,some 177100,some 134596,some 100947,some 74613,some 54264,some 38760,some 27132,some 18564,some 12376,some 8008,some 5005,some 3003,some 1716,some 924,some 462,some 210,some 84,some 28,some 7,some 1,none,none,none,none,none,none]
theorem bernsteinWeights82_identity : bernsteinWeights82=IntegerWeightedBernstein.weights 88 82 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights82_identity
def bernsteinRow82 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights82 affine01753)
theorem bernsteinRow82_weighted : bernsteinRow82=IntegerWeightedBernstein.applyWeights bernsteinWeights82 affine01753 := by decide +kernel
theorem bernsteinRow82_identity : bernsteinRow82=NestedInteger.coefficientFrom 88 82 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 82 0 affine01753 bernsteinRow82 bernsteinWeights82 bernsteinWeights82_identity bernsteinRow82_weighted
theorem bernsteinRow82_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow82=true := by decide +kernel
#print axioms bernsteinRow82_weighted
#print axioms bernsteinRow82_identity
#print axioms bernsteinRow82_positive
def bernsteinWeights83 : List (Option ℤ) := [some 39175752,some 36949857,some 34826302,some 32801517,some 30872016,some 29034396,some 27285336,some 25621596,some 24040016,some 22537515,some 21111090,some 19757815,some 18474840,some 17259390,some 16108764,some 15020334,some 13991544,some 13019909,some 12103014,some 11238513,some 10424128,some 9657648,some 8936928,some 8259888,some 7624512,some 7028847,some 6471002,some 5949147,some 5461512,some 5006386,some 4582116,some 4187106,some 3819816,some 3478761,some 3162510,some 2869685,some 2598960,some 2349060,some 2118760,some 1906884,some 1712304,some 1533939,some 1370754,some 1221759,some 1086008,some 962598,some 850668,some 749398,some 658008,some 575757,some 501942,some 435897,some 376992,some 324632,some 278256,some 237336,some 201376,some 169911,some 142506,some 118755,some 98280,some 80730,some 65780,some 53130,some 42504,some 33649,some 26334,some 20349,some 15504,some 11628,some 8568,some 6188,some 4368,some 3003,some 2002,some 1287,some 792,some 462,some 252,some 126,some 56,some 21,some 6,some 1,none,none,none,none,none]
theorem bernsteinWeights83_identity : bernsteinWeights83=IntegerWeightedBernstein.weights 88 83 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights83_identity
def bernsteinRow83 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights83 affine01753)
theorem bernsteinRow83_weighted : bernsteinRow83=IntegerWeightedBernstein.applyWeights bernsteinWeights83 affine01753 := by decide +kernel
theorem bernsteinRow83_identity : bernsteinRow83=NestedInteger.coefficientFrom 88 83 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 83 0 affine01753 bernsteinRow83 bernsteinWeights83 bernsteinWeights83_identity bernsteinRow83_weighted
theorem bernsteinRow83_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow83=true := by decide +kernel
#print axioms bernsteinRow83_weighted
#print axioms bernsteinRow83_identity
#print axioms bernsteinRow83_positive
def bernsteinWeights84 : List (Option ℤ) := [some 2331890,some 2225895,some 2123555,some 2024785,some 1929501,some 1837620,some 1749060,some 1663740,some 1581580,some 1502501,some 1426425,some 1353275,some 1282975,some 1215450,some 1150626,some 1088430,some 1028790,some 971635,some 916895,some 864501,some 814385,some 766480,some 720720,some 677040,some 635376,some 595665,some 557845,some 521855,some 487635,some 455126,some 424270,some 395010,some 367290,some 341055,some 316251,some 292825,some 270725,some 249900,some 230300,some 211876,some 194580,some 178365,some 163185,some 148995,some 135751,some 123410,some 111930,some 101270,some 91390,some 82251,some 73815,some 66045,some 58905,some 52360,some 46376,some 40920,some 35960,some 31465,some 27405,some 23751,some 20475,some 17550,some 14950,some 12650,some 10626,some 8855,some 7315,some 5985,some 4845,some 3876,some 3060,some 2380,some 1820,some 1365,some 1001,some 715,some 495,some 330,some 210,some 126,some 70,some 35,some 15,some 5,some 1,none,none,none,none]
theorem bernsteinWeights84_identity : bernsteinWeights84=IntegerWeightedBernstein.weights 88 84 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights84_identity
def bernsteinRow84 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights84 affine01753)
theorem bernsteinRow84_weighted : bernsteinRow84=IntegerWeightedBernstein.applyWeights bernsteinWeights84 affine01753 := by decide +kernel
theorem bernsteinRow84_identity : bernsteinRow84=NestedInteger.coefficientFrom 88 84 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 84 0 affine01753 bernsteinRow84 bernsteinWeights84 bernsteinWeights84_identity bernsteinRow84_weighted
theorem bernsteinRow84_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow84=true := by decide +kernel
#print axioms bernsteinRow84_weighted
#print axioms bernsteinRow84_identity
#print axioms bernsteinRow84_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
