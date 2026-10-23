/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinWeights20 : List (Option ℤ) := [some 30741195448351502730,some 6986635329170796075,some 1525816910968334775,some 319357027877093325,some 63871405575418665,some 12165982014365460,some 2198671448379300,some 375382930211100,some 60246643120300,some 9036996468045,some 1258315963905,some 161322559475,some 18855883575,some 1984829850,some 185250786,some 15020334,some 1028790,some 57155,some 2415,some 69,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights20_identity : bernsteinWeights20=IntegerWeightedBernstein.weights 88 20 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights20_identity
def bernsteinRow20 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights20 affine01753)
theorem bernsteinRow20_weighted : bernsteinRow20=IntegerWeightedBernstein.applyWeights bernsteinWeights20 affine01753 := by decide +kernel
theorem bernsteinRow20_identity : bernsteinRow20=NestedInteger.coefficientFrom 88 20 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 20 0 affine01753 bernsteinRow20 bernsteinWeights20 bernsteinWeights20_identity bernsteinRow20_weighted
theorem bernsteinRow20_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow20=true := by decide +kernel
#print axioms bernsteinRow20_weighted
#print axioms bernsteinRow20_identity
#print axioms bernsteinRow20_positive
def bernsteinWeights21 : List (Option ℤ) := [some 99542918594662008840,some 23754560119180706655,some 5460818418202461300,some 1206459883091241450,some 255485622301674660,some 51705423561053205,some 9967310565986160,some 1823288518168200,some 315136287090800,some 51209646652255,some 7778680504140,some 1096993404430,some 142466675900,some 16871053725,some 1799579064,some 170230452,some 13991544,some 971635,some 54740,some 2346,some 68,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights21_identity : bernsteinWeights21=IntegerWeightedBernstein.weights 88 21 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights21_identity
def bernsteinRow21 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights21 affine01753)
theorem bernsteinRow21_weighted : bernsteinRow21=IntegerWeightedBernstein.applyWeights bernsteinWeights21 affine01753 := by decide +kernel
theorem bernsteinRow21_identity : bernsteinRow21=NestedInteger.coefficientFrom 88 21 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 21 0 affine01753 bernsteinRow21 bernsteinWeights21 bernsteinWeights21_identity bernsteinRow21_weighted
theorem bernsteinRow21_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow21=true := by decide +kernel
#print axioms bernsteinRow21_weighted
#print axioms bernsteinRow21_identity
#print axioms bernsteinRow21_positive
def bernsteinWeights22 : List (Option ℤ) := [some 303153433901925208740,some 75788358475481302185,some 18293741700978245355,some 4254358535111219850,some 950974260789566790,some 203780198740621455,some 41738112995067045,some 8144022047817960,some 1508152231077400,some 263926640438545,some 43430966148115,some 6681687099710,some 954526728530,some 125595622175,some 15071474661,some 1629348612,some 156238908,some 13019909,some 916895,some 52394,some 2278,some 67,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights22_identity : bernsteinWeights22=IntegerWeightedBernstein.weights 88 22 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights22_identity
def bernsteinRow22 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights22 affine01753)
theorem bernsteinRow22_weighted : bernsteinRow22=IntegerWeightedBernstein.applyWeights bernsteinWeights22 affine01753 := by decide +kernel
theorem bernsteinRow22_identity : bernsteinRow22=NestedInteger.coefficientFrom 88 22 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 22 0 affine01753 bernsteinRow22 bernsteinWeights22 bernsteinWeights22_identity bernsteinRow22_weighted
theorem bernsteinRow22_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow22=true := by decide +kernel
#print axioms bernsteinRow22_weighted
#print axioms bernsteinRow22_identity
#print axioms bernsteinRow22_positive
def bernsteinWeights23 : List (Option ℤ) := [some 869918549457698425080,some 227365075426443906555,some 57494616774503056830,some 14039383165867025505,some 3303384274321653060,some 747194062048945335,some 162042085745554410,some 33594090947249085,some 6635869816740560,some 1244225590638855,some 220495674290430,some 36749279048405,some 5727160371180,some 828931106355,some 110524147514,some 13442126049,some 1473109704,some 143218999,some 12103014,some 864501,some 50116,some 2211,some 66,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights23_identity : bernsteinWeights23=IntegerWeightedBernstein.weights 88 23 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights23_identity
def bernsteinRow23 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights23 affine01753)
theorem bernsteinRow23_weighted : bernsteinRow23=IntegerWeightedBernstein.applyWeights bernsteinWeights23 affine01753 := by decide +kernel
theorem bernsteinRow23_identity : bernsteinRow23=NestedInteger.coefficientFrom 88 23 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 23 0 affine01753 bernsteinRow23 bernsteinWeights23 bernsteinWeights23_identity bernsteinRow23_weighted
theorem bernsteinRow23_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow23=true := by decide +kernel
#print axioms bernsteinRow23_weighted
#print axioms bernsteinRow23_identity
#print axioms bernsteinRow23_positive
def bernsteinWeights24 : List (Option ℤ) := [some 2356029404781266567925,some 642553474031254518525,some 169870458651940849725,some 43455233608636031325,some 10735998891545372445,some 2556190212272707725,some 585151976303390925,some 128447994798305325,some 26958221130508525,some 5391644226101705,some 1023729916348425,some 183746395242025,some 31022118677225,some 4898229264825,some 718406958841,some 97082021465,some 11969016345,some 1329890705,some 131115985,some 11238513,some 814385,some 47905,some 2145,some 65,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights24_identity : bernsteinWeights24=IntegerWeightedBernstein.weights 88 24 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights24_identity
def bernsteinRow24 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights24 affine01753)
theorem bernsteinRow24_weighted : bernsteinRow24=IntegerWeightedBernstein.applyWeights bernsteinWeights24 affine01753 := by decide +kernel
theorem bernsteinRow24_identity : bernsteinRow24=NestedInteger.coefficientFrom 88 24 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 24 0 affine01753 bernsteinRow24 bernsteinWeights24 bernsteinWeights24_identity bernsteinRow24_weighted
theorem bernsteinRow24_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow24=true := by decide +kernel
#print axioms bernsteinRow24_weighted
#print axioms bernsteinRow24_identity
#print axioms bernsteinRow24_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
