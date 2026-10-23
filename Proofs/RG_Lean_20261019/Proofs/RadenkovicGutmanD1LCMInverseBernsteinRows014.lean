/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinWeights70 : List (Option ℤ) := [some 2418561960739869780,some 1923856105133987325,some 1525816910968334775,some 1206459883091241450,some 950974260789566790,some 747194062048945335,some 585151976303390925,some 456703981505085600,some 355214207837288800,some 275291011073898820,some 212566476905162380,some 163512674542432600,some 125288932441604200,some 95615237915961100,some 72667580816130436,some 54991682779774384,some 41432089765583440,some 31074067324187580,some 23196134763125940,some 17231414395464984,some 12736262814039336,some 9364899127970100,some 6848956078664700,some 4981058966301600,some 3601688791018080,some 2588713818544245,some 1849081298960175,some 1312251244423350,some 925029565741050,some 647520696018735,some 449972009097765,some 310325523515700,some 212327989773900,some 144079707346575,some 96926348578605,some 64617565719070,some 42671977361650,some 27900908274925,some 18053528883775,some 11554258485616,some 7309837001104,some 4568648125690,some 2818953098830,some 1715884494940,some 1029530696964,some 608359048206,some 353697121050,some 202112640600,some 113380261800,some 62359143990,some 33578000610,some 17672631900,some 9075135300,some 4537567650,some 2203961430,some 1037158320,some 471435600,some 206253075,some 86493225,some 34597290,some 13123110,some 4686825,some 1562275,some 480700,some 134596,some 33649,some 7315,some 1330,some 190,some 19,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights70_identity : bernsteinWeights70=IntegerWeightedBernstein.weights 88 70 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights70_identity
def bernsteinRow70 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights70 affine01753)
theorem bernsteinRow70_weighted : bernsteinRow70=IntegerWeightedBernstein.applyWeights bernsteinWeights70 affine01753 := by decide +kernel
theorem bernsteinRow70_identity : bernsteinRow70=NestedInteger.coefficientFrom 88 70 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 70 0 affine01753 bernsteinRow70 bernsteinWeights70 bernsteinWeights70_identity bernsteinRow70_weighted
theorem bernsteinRow70_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow70=true := by decide +kernel
#print axioms bernsteinRow70_weighted
#print axioms bernsteinRow70_identity
#print axioms bernsteinRow70_positive
def bernsteinWeights71 : List (Option ℤ) := [some 613156553427009240,some 494705855605882455,some 398039194165652550,some 319357027877093325,some 255485622301674660,some 203780198740621455,some 162042085745554410,some 128447994798305325,some 101489773667796800,some 79923196763389980,some 62724534168736440,some 49053802362729780,some 38223742100828400,some 29673694525643100,some 22947657099830664,some 17675898036356052,some 13559593014190944,some 10358022441395860,some 7877932561061640,some 5964720367660956,some 4495151581425648,some 3371363686069236,some 2515943049305400,some 1867897112363100,some 1379370175283520,some 1012974972473835,some 739632519584070,some 536830054536825,some 387221678682300,some 277508869722315,some 197548686920970,some 139646485582065,some 97997533741800,some 68248282427325,some 47153358767970,some 32308782859535,some 21945588357420,some 14771069086725,some 9847379391150,some 6499270398159,some 4244421484512,some 2741188875414,some 1749695026860,some 1103068603890,some 686353797976,some 421171648758,some 254661927156,some 151584480450,some 88732378800,some 51021117810,some 28781143380,some 15905368710,some 8597496600,some 4537567650,some 2333606220,some 1166803110,some 565722720,some 265182525,some 119759850,some 51895935,some 21474180,some 8436285,some 3124550,some 1081575,some 346104,some 100947,some 26334,some 5985,some 1140,some 171,some 18,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights71_identity : bernsteinWeights71=IntegerWeightedBernstein.weights 88 71 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights71_identity
def bernsteinRow71 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights71 affine01753)
theorem bernsteinRow71_weighted : bernsteinRow71=IntegerWeightedBernstein.applyWeights bernsteinWeights71 affine01753 := by decide +kernel
theorem bernsteinRow71_identity : bernsteinRow71=NestedInteger.coefficientFrom 88 71 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 71 0 affine01753 bernsteinRow71 bernsteinWeights71 bernsteinWeights71_identity bernsteinRow71_weighted
theorem bernsteinRow71_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow71=true := by decide +kernel
#print axioms bernsteinRow71_weighted
#print axioms bernsteinRow71_identity
#print axioms bernsteinRow71_positive
def bernsteinWeights72 : List (Option ℤ) := [some 144773075114710515,some 118450697821126785,some 96666661440229905,some 78682166288559225,some 63871405575418665,some 51705423561053205,some 41738112995067045,some 33594090947249085,some 26958221130508525,some 21566576904406820,some 17198662594653540,some 13670731806006660,some 10830060261901380,some 8550047575185300,some 6726037425812436,some 5271759063474612,some 4116305022165108,some 3201570572795084,some 2480089880334220,some 1913212193400684,some 1469568786235308,some 1123787895356412,some 855420636763836,some 648045936942300,some 488526937079580,some 366395202809685,some 273342452889765,some 202802465047245,some 149608375854525,some 109712808959985,some 79960182801345,some 57902201338905,some 41648951840265,some 29749251314475,some 21094923659355,some 14844575908435,some 10363194502115,some 7174519270695,some 4923689695575,some 3348108992991,some 2254848913647,some 1503232609098,some 991493848554,some 646626422970,some 416714805914,some 265182149218,some 166509721602,some 103077446706,some 62852101650,some 37711260990,some 22239974430,some 12875774670,some 7307872110,some 4059928950,some 2203961430,some 1166803110,some 601080390,some 300540195,some 145422675,some 67863915,some 30421755,some 13037895,some 5311735,some 2042975,some 735471,some 245157,some 74613,some 20349,some 4845,some 969,some 153,some 17,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights72_identity : bernsteinWeights72=IntegerWeightedBernstein.weights 88 72 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights72_identity
def bernsteinRow72 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights72 affine01753)
theorem bernsteinRow72_weighted : bernsteinRow72=IntegerWeightedBernstein.applyWeights bernsteinWeights72 affine01753 := by decide +kernel
theorem bernsteinRow72_identity : bernsteinRow72=NestedInteger.coefficientFrom 88 72 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 72 0 affine01753 bernsteinRow72 bernsteinWeights72 bernsteinWeights72_identity bernsteinRow72_weighted
theorem bernsteinRow72_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow72=true := by decide +kernel
#print axioms bernsteinRow72_weighted
#print axioms bernsteinRow72_identity
#print axioms bernsteinRow72_positive
def bernsteinWeights73 : List (Option ℤ) := [some 31731084956648880,some 26322377293583730,some 21784036380896880,some 17984495151670680,some 14810760713140560,some 12165982014365460,some 9967310565986160,some 8144022047817960,some 6635869816740560,some 5391644226101705,some 4367914309753280,some 3527930788646880,some 2840671544105280,some 2280012686716080,some 1824010149372864,some 1454278362337824,some 1155454041309504,some 914734449370024,some 721480692460864,some 566877686933536,some 443643407165376,some 345780890878896,some 268367258592576,some 207374699821536,some 159518999862720,some 122131734269895,some 93052749919920,some 70539987842520,some 53194089192720,some 39895566894540,some 29752626158640,some 22057981462440,some 16253249498640,some 11899700525790,some 8654327655120,some 6250347750920,some 4481381406320,some 3188675231420,some 2250829575120,some 1575580702584,some 1093260079344,some 751616304549,some 511738760544,some 344867425584,some 229911617056,some 151532656696,some 98672427616,some 63432274896,some 40225345056,some 25140840660,some 15471286560,some 9364199760,some 5567902560,some 3247943160,some 1855967520,some 1037158320,some 565722720,some 300540195,some 155117520,some 77558760,some 37442160,some 17383860,some 7726160,some 3268760,some 1307504,some 490314,some 170544,some 54264,some 15504,some 3876,some 816,some 136,some 16,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights73_identity : bernsteinWeights73=IntegerWeightedBernstein.weights 88 73 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights73_identity
def bernsteinRow73 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights73 affine01753)
theorem bernsteinRow73_weighted : bernsteinRow73=IntegerWeightedBernstein.applyWeights bernsteinWeights73 affine01753 := by decide +kernel
theorem bernsteinRow73_identity : bernsteinRow73=NestedInteger.coefficientFrom 88 73 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 73 0 affine01753 bernsteinRow73 bernsteinWeights73 bernsteinWeights73_identity bernsteinRow73_weighted
theorem bernsteinRow73_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow73=true := by decide +kernel
#print axioms bernsteinRow73_weighted
#print axioms bernsteinRow73_identity
#print axioms bernsteinRow73_positive
def bernsteinWeights74 : List (Option ℤ) := [some 6431976680401800,some 5408707663065150,some 4538340912686850,some 3799541229226200,some 3173734438530120,some 2644778698775100,some 2198671448379300,some 1823288518168200,some 1508152231077400,some 1244225590638855,some 1023729916348425,some 839983521106400,some 687259244541600,some 560658857389200,some 456002537343216,some 369731787035040,some 298824321028320,some 240719591939480,some 193253756909160,some 154603005527328,some 123234279768160,some 97862516286480,some 77413632286320,some 60992558771040,some 47855699958816,some 37387265592825,some 29078984349975,some 22512762077400,some 17345898649800,some 13298522298180,some 10142940735900,some 7694644696200,some 5804731963800,some 4353548972850,some 3245372870670,some 2403979904200,some 1768966344600,some 1292706174900,some 937845656300,some 675248872536,some 482320623240,some 341643774795,some 239877544005,some 166871334960,some 114955808528,some 78378960360,some 52860229080,some 35240152720,some 23206929840,some 15084504396,some 9669554100,some 6107086800,some 3796297200,some 2319959400,some 1391975640,some 818809200,some 471435600,some 265182525,some 145422675,some 77558760,some 40116600,some 20058300,some 9657700,some 4457400,some 1961256,some 817190,some 319770,some 116280,some 38760,some 11628,some 3060,some 680,some 120,some 15,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights74_identity : bernsteinWeights74=IntegerWeightedBernstein.weights 88 74 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights74_identity
def bernsteinRow74 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights74 affine01753)
theorem bernsteinRow74_weighted : bernsteinRow74=IntegerWeightedBernstein.applyWeights bernsteinWeights74 affine01753 := by decide +kernel
theorem bernsteinRow74_identity : bernsteinRow74=NestedInteger.coefficientFrom 88 74 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 74 0 affine01753 bernsteinRow74 bernsteinWeights74 bernsteinWeights74_identity bernsteinRow74_weighted
theorem bernsteinRow74_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow74=true := by decide +kernel
#print axioms bernsteinRow74_weighted
#print axioms bernsteinRow74_identity
#print axioms bernsteinRow74_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
