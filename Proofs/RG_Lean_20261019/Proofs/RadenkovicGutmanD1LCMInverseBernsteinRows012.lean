/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinWeights60 : List (Option ℤ) := [some 73111821201089232081168,some 49848969000742658237160,some 33805622655676055586120,some 22799140860804781674360,some 15288835636069088887512,some 10192557090712725925008,some 6754104096255420793680,some 4447824648753569790960,some 2910305017085669122480,some 1891698261105684929612,some 1221222928055568752028,some 782835210292031251300,some 498167861094928978100,some 314632333323113038800,some 197169595549150837648,some 122564883719742412592,some 75553695443676829680,some 46171702771135840360,some 27963143931814663880,some 16777886359088798328,some 9969468706125227992,some 5864393356544251760,some 3413602103063071920,some 1965407271460556560,some 1118770292985239888,some 629308289804197437,some 349615716557887465,some 191724747789809255,some 103719945525634515,some 55317304280338408,some 29065024282889672,some 15033633249770520,some 7648690600760440,some 3824345300380220,some 1877405874732108,some 903936161908052,some 426384982032100,some 196793068630200,some 88749815264600,some 39049918716424,some 16735679449896,some 6973199770790,some 2818953098830,some 1103068603890,some 416714805914,some 151532656696,some 52860229080,some 17620076360,some 5586853480,some 1676056044,some 472733756,some 124403620,some 30260340,some 6724520,some 1344904,some 237336,some 35960,some 4495,some 435,some 29,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights60_identity : bernsteinWeights60=IntegerWeightedBernstein.weights 88 60 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights60_identity
def bernsteinRow60 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights60 affine01753)
theorem bernsteinRow60_weighted : bernsteinRow60=IntegerWeightedBernstein.applyWeights bernsteinWeights60 affine01753 := by decide +kernel
theorem bernsteinRow60_identity : bernsteinRow60=NestedInteger.coefficientFrom 88 60 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 60 0 affine01753 bernsteinRow60 bernsteinWeights60 bernsteinWeights60_identity bernsteinRow60_weighted
theorem bernsteinRow60_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow60=true := by decide +kernel
#print axioms bernsteinRow60_weighted
#print axioms bernsteinRow60_identity
#print axioms bernsteinRow60_positive
def bernsteinWeights61 : List (Option ℤ) := [some 33559524485745877020864,some 23262852200346573844008,some 16043346345066602651040,some 11006481794871273911760,some 7510305224735692786848,some 5096278545356362962504,some 3438452994457305131328,some 2306279447501851002720,some 1537519631667900668480,some 1018606755979984192868,some 670475333050116177584,some 438387717763537500728,some 284667349197102273200,some 183535527771815939300,some 117462737773962201152,some 74604711829408425056,some 47011188276065582912,some 29381992672540989320,some 18208558839321176480,some 11185257572725865552,some 6808417652963570336,some 4105075349580976232,some 2450791253481179840,some 1448194831602515360,some 846636978475316672,some 489462003181042451,some 279692573246309972,some 157890968768078210,some 88004802264174740,some 48402641245296107,some 26252279997448736,some 14031391033119152,some 7384942649010080,some 3824345300380220,some 1946939425648112,some 973469712824056,some 477551179875952,some 229591913401900,some 108043253365600,some 49699896548176,some 22314239266528,some 9762479679106,some 4154246671960,some 1715884494940,some 686353797976,some 265182149218,some 98672427616,some 35240152720,some 12033222880,some 3910797436,some 1203322288,some 348330136,some 94143280,some 23535820,some 5379616,some 1107568,some 201376,some 31465,some 4060,some 406,some 28,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights61_identity : bernsteinWeights61=IntegerWeightedBernstein.weights 88 61 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights61_identity
def bernsteinRow61 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights61 affine01753)
theorem bernsteinRow61_weighted : bernsteinRow61=IntegerWeightedBernstein.applyWeights bernsteinWeights61 affine01753 := by decide +kernel
theorem bernsteinRow61_identity : bernsteinRow61=NestedInteger.coefficientFrom 88 61 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 61 0 affine01753 bernsteinRow61 bernsteinWeights61 bernsteinWeights61_identity bernsteinRow61_weighted
theorem bernsteinRow61_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow61=true := by decide +kernel
#print axioms bernsteinRow61_weighted
#print axioms bernsteinRow61_identity
#print axioms bernsteinRow61_positive
def bernsteinWeights62 : List (Option ℤ) := [some 14614631630889333541344,some 10296672285399303176856,some 7219505855279971192968,some 5036864550195328739280,some 3496176570135581124912,some 2414026679379329824344,some 1657825550899057831176,some 1132173546955454128608,some 768759815833950334240,some 518912875687916475612,some 348131422929868015284,some 232087615286578676856,some 153720368566435227528,some 101131821425286333900,some 66072789997853738148,some 42858025944553776096,some 27593523553342842144,some 17629195603524593592,some 11173433833219812840,some 7023301266595310928,some 4376839919762295216,some 2703342303382594104,some 1654284096099796392,some 1002596421878664480,some 601557853127198688,some 357174975294274221,some 209769429934732479,some 121801604478231762,some 69886166503903470,some 39602161018878633,some 22150361247847371,some 12220888964329584,some 6646448384109072,some 3560597348629860,some 1877405874732108,some 973469712824056,some 495918532948104,some 247959266474052,some 121548660036300,some 58343356817424,some 27385657281648,some 12551759587422,some 5608233007146,some 2438362177020,some 1029530696964,some 421171648758,some 166509721602,some 63432274896,some 23206929840,some 8122425444,some 2707475148,some 854992152,some 254186856,some 70607460,some 18156204,some 4272048,some 906192,some 169911,some 27405,some 3654,some 378,some 27,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights62_identity : bernsteinWeights62=IntegerWeightedBernstein.weights 88 62 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights62_identity
def bernsteinRow62 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights62 affine01753)
theorem bernsteinRow62_weighted : bernsteinRow62=IntegerWeightedBernstein.applyWeights bernsteinWeights62 affine01753 := by decide +kernel
theorem bernsteinRow62_identity : bernsteinRow62=NestedInteger.coefficientFrom 88 62 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 62 0 affine01753 bernsteinRow62 bernsteinWeights62 bernsteinWeights62_identity bernsteinRow62_weighted
theorem bernsteinRow62_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow62=true := by decide +kernel
#print axioms bernsteinRow62_weighted
#print axioms bernsteinRow62_identity
#print axioms bernsteinRow62_positive
def bernsteinWeights63 : List (Option ℤ) := [some 6031435276240042413888,some 4317959345490030364488,some 3077166430119331983888,some 2182641305084642453688,some 1540687980059747614368,some 1082149890756251300568,some 756201128480271993168,some 525652003943603702568,some 363413731121503794368,some 249846940146033858628,some 170781452758048460328,some 116043807643289338428,some 78367246720143449328,some 52588547141148893628,some 35059031427432595752,some 23214764053299962052,some 15264502391210933952,some 9964327949818248552,some 6455761770304780752,some 4150132566624501912,some 2646461346833015712,some 1673497616379701112,some 1049058207282797712,some 651687674221131912,some 401038568751465792,some 244382877832924467,some 147405545359541742,some 87967825456500717,some 51915437974328292,some 30284005485024837,some 17451799771031262,some 9929472283517787,some 5574440580220512,some 3085851035479212,some 1683191473897752,some 903936161908052,some 477551179875952,some 247959266474052,some 126410606437752,some 63205303218876,some 30957699535776,some 14833897694226,some 6943526580276,some 3169870830126,some 1408831480056,some 608359048206,some 254661927156,some 103077446706,some 40225345056,some 15084504396,some 5414950296,some 1852482996,some 600805296,some 183579396,some 52451256,some 13884156,some 3365856,some 736281,some 142506,some 23751,some 3276,some 351,some 26,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights63_identity : bernsteinWeights63=IntegerWeightedBernstein.weights 88 63 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights63_identity
def bernsteinRow63 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights63 affine01753)
theorem bernsteinRow63_weighted : bernsteinRow63=IntegerWeightedBernstein.applyWeights bernsteinWeights63 affine01753 := by decide +kernel
theorem bernsteinRow63_identity : bernsteinRow63=NestedInteger.coefficientFrom 88 63 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 63 0 affine01753 bernsteinRow63 bernsteinWeights63 bernsteinWeights63_identity bernsteinRow63_weighted
theorem bernsteinRow63_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow63=true := by decide +kernel
#print axioms bernsteinRow63_weighted
#print axioms bernsteinRow63_identity
#print axioms bernsteinRow63_positive
def bernsteinWeights64 : List (Option ℤ) := [some 2356029404781266567925,some 1713475930750012049400,some 1240792915370698380600,some 894525125034689530200,some 641953325024894839320,some 458538089303496313800,some 325948762275979307400,some 230549124536668290600,some 162238272822099908200,some 113566790975469935740,some 79065487387985398300,some 54737645114759121900,some 37676560923145889100,some 25778699578994555700,some 17529515713716297876,some 11844267374132633700,some 7950261662089028100,some 5300174441392685400,some 3508566179513467800,some 2305629203680278840,some 1503671219791486200,some 972963730453314600,some 624439409096903400,some 397370533061665800,some 250649105469666120,some 156655690918541325,some 96977332473382725,some 59437719903041025,some 36052387482172425,some 21631432489303455,some 12832205713993575,some 7522327487513475,some 4355031703297275,some 2488589544741300,some 1402659561581460,some 779255311989700,some 426384982032100,some 229591913401900,some 121548660036300,some 63205303218876,some 32247603683100,some 16123801841550,some 7890371113950,some 3773655750150,some 1761039350070,some 800472431850,some 353697121050,some 151584480450,some 62852101650,some 25140840660,some 9669554100,some 3562467300,some 1251677700,some 417225900,some 131128140,some 38567100,some 10518300,some 2629575,some 593775,some 118755,some 20475,some 2925,some 325,some 25,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights64_identity : bernsteinWeights64=IntegerWeightedBernstein.weights 88 64 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights64_identity
def bernsteinRow64 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights64 affine01753)
theorem bernsteinRow64_weighted : bernsteinRow64=IntegerWeightedBernstein.applyWeights bernsteinWeights64 affine01753 := by decide +kernel
theorem bernsteinRow64_identity : bernsteinRow64=NestedInteger.coefficientFrom 88 64 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 64 0 affine01753 bernsteinRow64 bernsteinWeights64 bernsteinWeights64_identity bernsteinRow64_weighted
theorem bernsteinRow64_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow64=true := by decide +kernel
#print axioms bernsteinRow64_weighted
#print axioms bernsteinRow64_identity
#print axioms bernsteinRow64_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
