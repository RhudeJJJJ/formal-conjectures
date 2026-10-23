/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinWeights55 : List (Option ℤ) := [some 1682429504296032856718256,some 1051518440185020535448910,some 652666618045874815106220,some 402224776237574013960810,some 246066921933574690893672,some 149397774031098919471158,some 89998659054878867151300,some 53779686508403225492850,some 31869443856831541032800,some 18723298265888530356770,some 10902173673808511346980,some 6289715581043371930950,some 3594123189167641103400,some 2033517067555375887450,some 1138769557831010496972,some 630939890149613923998,some 345720487753213109040,some 187265264199657100730,some 100226479430802391940,some 52976853413424121454,some 27640097433090845976,some 14226520737620288370,some 7219428434016265740,some 3609714217008132870,some 1777090076065542336,some 860778005594247069,some 409894288378212890,some 191724747789809255,some 88004802264174740,some 39602161018878633,some 17451799771031262,some 7522327487513475,some 3167295784216200,some 1300853625660225,some 520341450264090,some 202355008436035,some 76360380541900,some 27900908274925,some 9847379391150,some 3348108992991,some 1093260079344,some 341643774795,some 101766230790,some 28760021745,some 7669339132,some 1917334783,some 445891810,some 95548245,some 18643560,some 3262623,some 501942,some 66045,some 7140,some 595,some 34,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights55_identity : bernsteinWeights55=IntegerWeightedBernstein.weights 88 55 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights55_identity
def bernsteinRow55 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights55 affine01753)
theorem bernsteinRow55_weighted : bernsteinRow55=IntegerWeightedBernstein.applyWeights bernsteinWeights55 affine01753 := by decide +kernel
theorem bernsteinRow55_identity : bernsteinRow55=NestedInteger.coefficientFrom 88 55 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 55 0 affine01753 bernsteinRow55 bernsteinWeights55 bernsteinWeights55_identity bernsteinRow55_weighted
theorem bernsteinRow55_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow55=true := by decide +kernel
#print axioms bernsteinRow55_weighted
#print axioms bernsteinRow55_identity
#print axioms bernsteinRow55_positive
def bernsteinWeights56 : List (Option ℤ) := [some 991431672174447933423258,some 630911064111012321269346,some 398851822139145720342690,some 250441841808300801145410,some 156157854303999323067138,some 96669147902475771422514,some 59399114976220052319858,some 36218972546475641658450,some 21910242651571684460050,some 13146145590943010676030,some 7821124592080019009790,some 4612458092765139416030,some 2695592391875730827550,some 1560606121612265215950,some 894747509724365390478,some 507829667681396572974,some 285219402396400814958,some 158455223553556008310,some 87038784768854708790,some 47249626017378270486,some 25336755980333275478,some 13413576695470557606,some 7007092303604022630,some 3609714217008132870,some 1832624140942590534,some 916312070471295267,some 450883717216034179,some 218169540588403635,some 103719945525634515,some 48402641245296107,some 22150361247847371,some 9929472283517787,some 4355031703297275,some 1866442158555975,some 780512175396135,some 317986441828055,some 125994627894135,some 48459472266975,some 18053528883775,some 6499270398159,some 2254848913647,some 751616304549,some 239877544005,some 73006209045,some 21090682613,some 5752004349,some 1471442973,some 350343565,some 76904685,some 15380937,some 2760681,some 435897,some 58905,some 6545,some 561,some 33,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights56_identity : bernsteinWeights56=IntegerWeightedBernstein.weights 88 56 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights56_identity
def bernsteinRow56 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights56 affine01753)
theorem bernsteinRow56_weighted : bernsteinRow56=IntegerWeightedBernstein.applyWeights bernsteinWeights56 affine01753 := by decide +kernel
theorem bernsteinRow56_identity : bernsteinRow56=NestedInteger.coefficientFrom 88 56 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 56 0 affine01753 bernsteinRow56 bernsteinWeights56 bernsteinWeights56_identity bernsteinRow56_weighted
theorem bernsteinRow56_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow56=true := by decide +kernel
#print axioms bernsteinRow56_weighted
#print axioms bernsteinRow56_identity
#print axioms bernsteinRow56_positive
def bernsteinWeights57 : List (Option ℤ) := [some 556593219466356734553408,some 360520608063435612153912,some 232059241971866600926656,some 148409980330844919197280,some 94283987504301478078272,some 59488706401523551644624,some 37270032926255719102656,some 23180142429744410661408,some 14308729894903957198400,some 8764097060628673784020,some 5325020998862991666240,some 3208666499314879593760,some 1916865700889408588480,some 1134986270263465611600,some 665858611887899825472,some 386917842042968817504,some 222610265284995758016,some 126764178842844806648,some 71416438784701299520,some 39789158751476438304,some 21912870037044995008,some 11923179284862717872,some 6406484391866534976,some 3397378086595889760,some 1777090076065542336,some 916312070471295267,some 465428353255261088,some 232714176627630544,some 114449595062769120,some 55317304280338408,some 26252279997448736,some 12220888964329584,some 5574440580220512,some 2488589544741300,some 1085929983159840,some 462525733568080,some 191991813933920,some 77535155627160,some 30405943383200,some 11554258485616,some 4244421484512,some 1503232609098,some 511738760544,some 166871334960,some 51915526432,some 15338678264,some 4280561376,some 1121099408,some 273438880,some 61523748,some 12620256,some 2324784,some 376992,some 52360,some 5984,some 528,some 32,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights57_identity : bernsteinWeights57=IntegerWeightedBernstein.weights 88 57 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights57_identity
def bernsteinRow57 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights57 affine01753)
theorem bernsteinRow57_weighted : bernsteinRow57=IntegerWeightedBernstein.applyWeights bernsteinWeights57 affine01753 := by decide +kernel
theorem bernsteinRow57_identity : bernsteinRow57=NestedInteger.coefficientFrom 88 57 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 57 0 affine01753 bernsteinRow57 bernsteinWeights57 bernsteinWeights57_identity bernsteinRow57_weighted
theorem bernsteinRow57_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow57=true := by decide +kernel
#print axioms bernsteinRow57_weighted
#print axioms bernsteinRow57_identity
#print axioms bernsteinRow57_positive
def bernsteinWeights58 : List (Option ℤ) := [some 297489479369949289157856,some 196072611402921122399496,some 128461366091569011227256,some 83649261641021681729376,some 54125992826543441119008,some 34795281102777926433648,some 22218673475267832541968,some 14089890496511308441248,some 8871412534840453463008,some 5544632834275283414380,some 3439076061765682117780,some 2116354499548112072480,some 1291800798425471005280,some 781879430625942976880,some 469127658375565786128,some 278940769844931007968,some 164307576757973059488,some 95846086442150951368,some 55347740058143507128,some 31627280033224861216,some 17876288714431443296,some 9989690752182277136,some 5516694892996182896,some 3009106305270645216,some 1620288010530347424,some 860778005594247069,some 450883717216034179,some 232714176627630544,some 118264581564861424,some 59132290782430712,some 29065024282889672,some 14031391033119152,some 6646448384109072,some 3085851035479212,some 1402659561581460,some 623404249591760,some 270533919634160,some 114456658306760,some 47129212243960,some 18851684897584,some 7309837001104,some 2741188875414,some 991493848554,some 344867425584,some 114955808528,some 36576848168,some 11058116888,some 3159461968,some 847660528,some 211915132,some 48903492,some 10295472,some 1947792,some 324632,some 46376,some 5456,some 496,some 31,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights58_identity : bernsteinWeights58=IntegerWeightedBernstein.weights 88 58 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights58_identity
def bernsteinRow58 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights58 affine01753)
theorem bernsteinRow58_weighted : bernsteinRow58=IntegerWeightedBernstein.applyWeights bernsteinWeights58 affine01753 := by decide +kernel
theorem bernsteinRow58_identity : bernsteinRow58=NestedInteger.coefficientFrom 88 58 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 58 0 affine01753 bernsteinRow58 bernsteinWeights58 bernsteinWeights58_identity bernsteinRow58_weighted
theorem bernsteinRow58_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow58=true := by decide +kernel
#print axioms bernsteinRow58_weighted
#print axioms bernsteinRow58_identity
#print axioms bernsteinRow58_positive
def bernsteinWeights59 : List (Option ℤ) := [some 151265836967770824995520,some 101416867967028166758360,some 67611245311352111172240,some 44812104450547329497880,some 29523268814478240610368,some 19330711723765514685360,some 12576607627510093891680,some 8128782978756524100720,some 5218477961670854978240,some 3326779700565170048628,some 2105556772509601296600,some 1322721562217570045300,some 824553701122641067200,some 509921367799528028400,some 312751772250377190752,some 190186888530634778160,some 114633193086957948480,some 68461490315822108120,some 40498346384007444240,some 23720460024918645912,some 13750991318793417920,some 7886597962249166160,some 4472995859186094240,some 2507588587725537680,some 1388818294740297792,some 759510004936100355,some 409894288378212890,some 218169540588403635,some 114449595062769120,some 59132290782430712,some 30067266499541040,some 15033633249770520,some 7384942649010080,some 3560597348629860,some 1683191473897752,some 779255311989700,some 352870329957600,some 156077261327400,some 67327446062800,some 28277527346376,some 11541847896480,some 4568648125690,some 1749695026860,some 646626422970,some 229911617056,some 78378960360,some 25518731280,some 7898654920,some 2311801440,some 635745396,some 163011640,some 38608020,some 8347680,some 1623160,some 278256,some 40920,some 4960,some 465,some 30,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights59_identity : bernsteinWeights59=IntegerWeightedBernstein.weights 88 59 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights59_identity
def bernsteinRow59 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights59 affine01753)
theorem bernsteinRow59_weighted : bernsteinRow59=IntegerWeightedBernstein.applyWeights bernsteinWeights59 affine01753 := by decide +kernel
theorem bernsteinRow59_identity : bernsteinRow59=NestedInteger.coefficientFrom 88 59 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 59 0 affine01753 bernsteinRow59 bernsteinWeights59 bernsteinWeights59_identity bernsteinRow59_weighted
theorem bernsteinRow59_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow59=true := by decide +kernel
#print axioms bernsteinRow59_weighted
#print axioms bernsteinRow59_identity
#print axioms bernsteinRow59_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
