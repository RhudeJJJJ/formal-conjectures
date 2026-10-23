/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinWeights65 : List (Option ℤ) := [some 869918549457698425080,some 642553474031254518525,some 472683015379313668800,some 346267790336008850400,some 252571800009794690880,some 183415235721398525520,some 132589327027517006400,some 95399637739311016800,some 68310851714568382400,some 48671481846629972460,some 34501303587484537440,some 24327842273226276400,some 17061084191613232800,some 11897861344151333400,some 8249183865278257824,some 5685248339583664176,some 3894005712043605600,some 2650087220696342700,some 1791608261879217600,some 1202936975833188960,some 801957983888792640,some 530707489338171600,some 348524321356411200,some 227068876035237600,some 146721427591999680,some 93993414551124795,some 59678358445158600,some 37539612570341700,some 23385332420868600,some 14420954992868970,some 8799226775309880,some 5309878226480100,some 3167295784216200,some 1866442158555975,some 1085929983159840,some 623404249591760,some 352870329957600,some 196793068630200,some 108043253365600,some 58343356817424,some 30957699535776,some 16123801841550,some 8233430727600,some 4116715363800,some 2012616400080,some 960566918220,some 446775310800,some 202112640600,some 88732378800,some 37711260990,some 15471286560,some 6107086800,some 2310789600,some 834451800,some 286097760,some 92561040,some 28048800,some 7888725,some 2035800,some 475020,some 98280,some 17550,some 2600,some 300,some 24,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights65_identity : bernsteinWeights65=IntegerWeightedBernstein.weights 88 65 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights65_identity
def bernsteinRow65 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights65 affine01753)
theorem bernsteinRow65_weighted : bernsteinRow65=IntegerWeightedBernstein.applyWeights bernsteinWeights65 affine01753 := by decide +kernel
theorem bernsteinRow65_identity : bernsteinRow65=NestedInteger.coefficientFrom 88 65 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 65 0 affine01753 bernsteinRow65 bernsteinWeights65 bernsteinWeights65_identity bernsteinRow65_weighted
theorem bernsteinRow65_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow65=true := by decide +kernel
#print axioms bernsteinRow65_weighted
#print axioms bernsteinRow65_identity
#print axioms bernsteinRow65_positive
def bernsteinWeights66 : List (Option ℤ) := [some 303153433901925208740,some 227365075426443906555,some 169870458651940849725,some 126415225043304818400,some 93695990326214159520,some 69156564288396165360,some 50825908693881519120,some 37189689288205989600,some 27088786024742634400,some 19639369867938409940,some 14170178259145435020,some 10173461314258261040,some 7266758081613043600,some 5163222847461899400,some 3648677478873075576,some 2563935525694593648,some 1791242627540058576,some 1243918491347262900,some 858478958817125100,some 588671286046028640,some 400978991944396320,some 271250494550621040,some 182183167981760400,some 121455445321173600,some 80347448443237920,some 52728013040874885,some 34315056105966195,some 22138745874816900,some 14154280149473100,some 8964377427999630,some 5621728217559090,some 3489348548829780,some 2142582442263900,some 1300853625660225,some 780512175396135,some 462525733568080,some 270533919634160,some 156077261327400,some 88749815264600,some 49699896548176,some 27385657281648,some 14833897694226,some 7890371113950,some 4116715363800,some 2104098963720,some 1052049481860,some 513791607420,some 244662670200,some 113380261800,some 51021117810,some 22239974430,some 9364199760,some 3796297200,some 1476337800,some 548354040,some 193536720,some 64512240,some 20160075,some 5852925,some 1560780,some 376740,some 80730,some 14950,some 2300,some 276,some 23,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights66_identity : bernsteinWeights66=IntegerWeightedBernstein.weights 88 66 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights66_identity
def bernsteinRow66 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights66 affine01753)
theorem bernsteinRow66_weighted : bernsteinRow66=IntegerWeightedBernstein.applyWeights bernsteinWeights66 affine01753 := by decide +kernel
theorem bernsteinRow66_identity : bernsteinRow66=NestedInteger.coefficientFrom 88 66 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 66 0 affine01753 bernsteinRow66 bernsteinWeights66 bernsteinWeights66_identity bernsteinRow66_weighted
theorem bernsteinRow66_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow66=true := by decide +kernel
#print axioms bernsteinRow66_weighted
#print axioms bernsteinRow66_identity
#print axioms bernsteinRow66_positive
def bernsteinWeights67 : List (Option ℤ) := [some 99542918594662008840,some 75788358475481302185,some 57494616774503056830,some 43455233608636031325,some 32719234717090658880,some 24539426037817994160,some 18330655594514646240,some 13636219405675529520,some 10100903263463355200,some 7449416156804224460,some 5469191608792974920,some 3996716944887173980,some 2906703232645217440,some 2103535234151144200,some 1514545368588823824,some 1084741953178481928,some 772692898154535072,some 547324136192795676,some 385439532530137800,some 269807672771096460,some 187692294101632320,some 129728497393775280,some 89067326568860640,some 60727722660586800,some 41107996877935680,some 27619435402363035,some 18412956934908690,some 12176310231149295,some 7984465725343800,some 5189902721473470,some 3342649210440540,some 2132379668729310,some 1346766106565880,some 841728816603675,some 520341450264090,some 317986441828055,some 191991813933920,some 114456658306760,some 67327446062800,some 39049918716424,some 22314239266528,some 12551759587422,some 6943526580276,some 3773655750150,some 2012616400080,some 1052049481860,some 538257874440,some 269128937220,some 131282408400,some 62359143990,some 28781143380,some 12875774670,some 5567902560,some 2319959400,some 927983760,some 354817320,some 129024480,some 44352165,some 14307150,some 4292145,some 1184040,some 296010,some 65780,some 12650,some 2024,some 253,some 22,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights67_identity : bernsteinWeights67=IntegerWeightedBernstein.weights 88 67 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights67_identity
def bernsteinRow67 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights67 affine01753)
theorem bernsteinRow67_weighted : bernsteinRow67=IntegerWeightedBernstein.applyWeights bernsteinWeights67 affine01753 := by decide +kernel
theorem bernsteinRow67_identity : bernsteinRow67=NestedInteger.coefficientFrom 88 67 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 67 0 affine01753 bernsteinRow67 bernsteinWeights67 bernsteinWeights67_identity bernsteinRow67_weighted
theorem bernsteinRow67_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow67=true := by decide +kernel
#print axioms bernsteinRow67_weighted
#print axioms bernsteinRow67_identity
#print axioms bernsteinRow67_positive
def bernsteinWeights68 : List (Option ℤ) := [some 30741195448351502730,some 23754560119180706655,some 18293741700978245355,some 14039383165867025505,some 10735998891545372445,some 8179808679272664720,some 6208770443303347920,some 4694436188839116720,some 3535316142212174320,some 2651487106659130740,some 1980224548011249540,some 1472474663905800940,some 1090013712241956540,some 803167998494073240,some 588989865562320376,some 429803415410341896,some 312049055023946856,some 225368761961739396,some 161884603662657876,some 115631859759041340,some 82115378669464140,some 57963796707857040,some 40661170824914640,some 28339603908273840,some 19619725782651120,some 13488561475572645,some 9206478467454345,some 6236646703759395,some 4191844505805495,some 2794563003870330,some 1847253511032930,some 1210269541711230,some 785613562163430,some 505037289962205,some 321387366339585,some 202355008436035,some 125994627894135,some 77535155627160,some 47129212243960,some 28277527346376,some 16735679449896,some 9762479679106,some 5608233007146,some 3169870830126,some 1761039350070,some 960566918220,some 513791607420,some 269128937220,some 137846528820,some 68923264410,some 33578000610,some 15905368710,some 7307872110,some 3247943160,some 1391975640,some 573166440,some 225792840,some 84672315,some 30045015,some 10015005,some 3108105,some 888030,some 230230,some 53130,some 10626,some 1771,some 231,some 21,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights68_identity : bernsteinWeights68=IntegerWeightedBernstein.weights 88 68 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights68_identity
def bernsteinRow68 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights68 affine01753)
theorem bernsteinRow68_weighted : bernsteinRow68=IntegerWeightedBernstein.applyWeights bernsteinWeights68 affine01753 := by decide +kernel
theorem bernsteinRow68_identity : bernsteinRow68=NestedInteger.coefficientFrom 88 68 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 68 0 affine01753 bernsteinRow68 bernsteinWeights68 bernsteinWeights68_identity bernsteinRow68_weighted
theorem bernsteinRow68_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow68=true := by decide +kernel
#print axioms bernsteinRow68_weighted
#print axioms bernsteinRow68_identity
#print axioms bernsteinRow68_positive
def bernsteinWeights69 : List (Option ℤ) := [some 8910491434304783400,some 6986635329170796075,some 5460818418202461300,some 4254358535111219850,some 3303384274321653060,some 2556190212272707725,some 1971038235969316800,some 1514334254464231200,some 1159120046626942400,some 883829035553043580,some 671262558647881200,some 507749884105448600,some 382460951663844400,some 286845713747883300,some 214178132931752864,some 159186450151978480,some 117754360386395040,some 86680293062207460,some 63484158299081520,some 46252743903616536,some 33516481089577200,some 24151581961607100,some 17302625882942400,some 12321566916640800,some 8719878125622720,some 6131164307078475,some 4282083008118300,some 2969831763694950,some 2044802197953900,some 1397281501935165,some 947309492837400,some 636983969321700,some 424655979547800,some 280576272201225,some 183649923622620,some 119032357903550,some 76360380541900,some 48459472266975,some 30405943383200,some 18851684897584,some 11541847896480,some 6973199770790,some 4154246671960,some 2438362177020,some 1408831480056,some 800472431850,some 446775310800,some 244662670200,some 131282408400,some 68923264410,some 35345263800,some 17672631900,some 8597496600,some 4059928950,some 1855967520,some 818809200,some 347373600,some 141120525,some 54627300,some 20030010,some 6906900,some 2220075,some 657800,some 177100,some 42504,some 8855,some 1540,some 210,some 20,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights69_identity : bernsteinWeights69=IntegerWeightedBernstein.weights 88 69 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights69_identity
def bernsteinRow69 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights69 affine01753)
theorem bernsteinRow69_weighted : bernsteinRow69=IntegerWeightedBernstein.applyWeights bernsteinWeights69 affine01753 := by decide +kernel
theorem bernsteinRow69_identity : bernsteinRow69=NestedInteger.coefficientFrom 88 69 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 69 0 affine01753 bernsteinRow69 bernsteinWeights69 bernsteinWeights69_identity bernsteinRow69_weighted
theorem bernsteinRow69_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow69=true := by decide +kernel
#print axioms bernsteinRow69_weighted
#print axioms bernsteinRow69_identity
#print axioms bernsteinRow69_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
