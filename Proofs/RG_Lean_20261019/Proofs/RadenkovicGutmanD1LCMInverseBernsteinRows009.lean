/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def bernsteinWeights45 : List (Option ℤ) := [some 25665205262091854495873760,some 13124252690842425594480900,some 6637553085023755473070800,some 3318776542511877736535400,some 1639866056299986646288080,some 800410813194041101164420,some 385740150936887277669600,some 183461779104129314989200,some 86068488962431036661600,some 39806676145124354455990,some 18139751154740212157160,some 8139631928409069557700,some 3594123189167641103400,some 1560606121612265215950,some 665858611887899825472,some 278940769844931007968,some 114633193086957948480,some 46171702771135840360,some 18208558839321176480,some 7023301266595310928,some 2646461346833015712,some 972963730453314600,some 348524321356411200,some 121455445321173600,some 41107996877935680,some 13488561475572645,some 4282083008118300,some 1312251244423350,some 387221678682300,some 109712808959985,some 29752626158640,some 7694644696200,some 1889912732400,some 438729741450,some 95722852680,some 19499099620,some 3679075400,some 636763050,some 99884400,some 13983816,some 1712304,some 178365,some 15180,some 990,some 44,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights45_identity : bernsteinWeights45=IntegerWeightedBernstein.weights 88 45 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights45_identity
def bernsteinRow45 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights45 affine01753)
theorem bernsteinRow45_weighted : bernsteinRow45=IntegerWeightedBernstein.applyWeights bernsteinWeights45 affine01753 := by decide +kernel
theorem bernsteinRow45_identity : bernsteinRow45=NestedInteger.coefficientFrom 88 45 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 45 0 affine01753 bernsteinRow45 bernsteinWeights45 bernsteinWeights45_identity bernsteinRow45_weighted
theorem bernsteinRow45_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow45=true := by decide +kernel
#print axioms bernsteinRow45_weighted
#print axioms bernsteinRow45_identity
#print axioms bernsteinRow45_positive
def bernsteinWeights46 : List (Option ℤ) := [some 23991387527607603115708080,some 12540952571249428901392860,some 6486699605818670121410100,some 3318776542511877736535400,some 1678910486211891090247320,some 839455243105945545123660,some 414670662257153823494820,some 202278371832757962680400,some 97393290141698278327600,some 46261812817306682205610,some 21666924990384142298830,some 10000119226331142599460,some 4545508739241428454300,some 2033517067555375887450,some 894747509724365390478,some 386917842042968817504,some 164307576757973059488,some 68461490315822108120,some 27963143931814663880,some 11185257572725865552,some 4376839919762295216,some 1673497616379701112,some 624439409096903400,some 227068876035237600,some 80347448443237920,some 27619435402363035,some 9206478467454345,some 2969831763694950,some 925029565741050,some 277508869722315,some 79960182801345,some 22057981462440,some 5804731963800,some 1451182990950,some 343006888770,some 76223753060,some 15820024220,some 3042312350,some 536878650,some 85900584,some 12271512,some 1533939,some 163185,some 14190,some 946,some 43,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights46_identity : bernsteinWeights46=IntegerWeightedBernstein.weights 88 46 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights46_identity
def bernsteinRow46 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights46 affine01753)
theorem bernsteinRow46_weighted : bernsteinRow46=IntegerWeightedBernstein.applyWeights bernsteinWeights46 affine01753 := by decide +kernel
theorem bernsteinRow46_identity : bernsteinRow46=NestedInteger.coefficientFrom 88 46 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 46 0 affine01753 bernsteinRow46 bernsteinWeights46 bernsteinWeights46_identity bernsteinRow46_weighted
theorem bernsteinRow46_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow46=true := by decide +kernel
#print axioms bernsteinRow46_weighted
#print axioms bernsteinRow46_identity
#print axioms bernsteinRow46_positive
def bernsteinWeights47 : List (Option ℤ) := [some 21439112258713177252334880,some 11450434956358174214315220,some 6054252965430758779982760,some 3167923063306792384874700,some 1639866056299986646288080,some 839455243105945545123660,some 424784580848791721628840,some 212392290424395860814420,some 104885081691059684352800,some 51131477324391596121990,some 24594887826922539906780,some 11666805764052999699370,some 5454610487089714145160,some 2511991671686052566850,some 1138769557831010496972,some 507829667681396572974,some 222610265284995758016,some 95846086442150951368,some 40498346384007444240,some 16777886359088798328,some 6808417652963570336,some 2703342303382594104,some 1049058207282797712,some 397370533061665800,some 146721427591999680,some 52728013040874885,some 18412956934908690,some 6236646703759395,some 2044802197953900,some 647520696018735,some 197548686920970,some 57902201338905,some 16253249498640,some 4353548972850,some 1108176102180,some 266783135710,some 60403728840,some 12777711870,some 2505433700,some 450978066,some 73629072,some 10737573,some 1370754,some 148995,some 13244,some 903,some 42,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights47_identity : bernsteinWeights47=IntegerWeightedBernstein.weights 88 47 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights47_identity
def bernsteinRow47 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights47 affine01753)
theorem bernsteinRow47_weighted : bernsteinRow47=IntegerWeightedBernstein.applyWeights bernsteinWeights47 affine01753 := by decide +kernel
theorem bernsteinRow47_identity : bernsteinRow47=NestedInteger.coefficientFrom 88 47 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 47 0 affine01753 bernsteinRow47 bernsteinWeights47 bernsteinWeights47_identity bernsteinRow47_weighted
theorem bernsteinRow47_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow47=true := by decide +kernel
#print axioms bernsteinRow47_weighted
#print axioms bernsteinRow47_identity
#print axioms bernsteinRow47_positive
def bernsteinWeights48 : List (Option ℤ) := [some 18312575054317505569702710,some 9988677302355003038019660,some 5396181990927415434332460,some 2886329902123966395108060,some 1528057007006805738586620,some 800410813194041101164420,some 414670662257153823494820,some 212392290424395860814420,some 107507208733336176461620,some 53753604366668088230810,some 26536589497469056215210,some 12928082062869540207410,some 6212195276963285554210,some 2942618815403661578310,some 1373222113855042069878,some 630939890149613923998,some 285219402396400814958,some 126764178842844806648,some 55347740058143507128,some 23720460024918645912,some 9969468706125227992,some 4105075349580976232,some 1654284096099796392,some 651687674221131912,some 250649105469666120,some 93993414551124795,some 34315056105966195,some 12176310231149295,some 4191844505805495,some 1397281501935165,some 449972009097765,some 139646485582065,some 41648951840265,some 11899700525790,some 3245372870670,some 841392966470,some 206379406870,some 47626016970,some 10272278170,some 2054455634,some 377348994,some 62891499,some 9366819,some 1221759,some 135751,some 12341,some 861,some 41,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights48_identity : bernsteinWeights48=IntegerWeightedBernstein.weights 88 48 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights48_identity
def bernsteinRow48 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights48 affine01753)
theorem bernsteinRow48_weighted : bernsteinRow48=IntegerWeightedBernstein.applyWeights bernsteinWeights48 affine01753 := by decide +kernel
theorem bernsteinRow48_identity : bernsteinRow48=NestedInteger.coefficientFrom 88 48 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 48 0 affine01753 bernsteinRow48 bernsteinWeights48 bernsteinWeights48_identity bernsteinRow48_weighted
theorem bernsteinRow48_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow48=true := by decide +kernel
#print axioms bernsteinRow48_weighted
#print axioms bernsteinRow48_identity
#print axioms bernsteinRow48_positive
def bernsteinWeights49 : List (Option ℤ) := [some 14949040860667351485471600,some 8323897751962502531683050,some 4592495311427587603687200,some 2509852088803449039224400,some 1358272895117160656521440,some 727646193812764637422200,some 385740150936887277669600,some 202278371832757962680400,some 104885081691059684352800,some 53753604366668088230810,some 27217014869199032015600,some 13608507434599516007800,some 6715886785906254653200,some 3269576461559623975900,some 1569396701548619508432,some 742282223705428145880,some 345720487753213109040,some 158455223553556008310,some 71416438784701299520,some 31627280033224861216,some 13750991318793417920,some 5864393356544251760,some 2450791253481179840,some 1002596421878664480,some 401038568751465792,some 156655690918541325,some 59678358445158600,some 22138745874816900,some 7984465725343800,some 2794563003870330,some 947309492837400,some 310325523515700,some 97997533741800,some 29749251314475,some 8654327655120,some 2403979904200,some 635013559600,some 158753389900,some 37353738800,some 8217822536,some 1677106640,some 314457495,some 53524680,some 8145060,some 1086008,some 123410,some 11480,some 820,some 40,some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem bernsteinWeights49_identity : bernsteinWeights49=IntegerWeightedBernstein.weights 88 49 0 affine01753 := by decide +kernel
#print axioms bernsteinWeights49_identity
def bernsteinRow49 : NestedInteger.Poly 2 := rg_integer_row%
  (IntegerWeightedBernstein.applyWeights bernsteinWeights49 affine01753)
theorem bernsteinRow49_weighted : bernsteinRow49=IntegerWeightedBernstein.applyWeights bernsteinWeights49 affine01753 := by decide +kernel
theorem bernsteinRow49_identity : bernsteinRow49=NestedInteger.coefficientFrom 88 49 0 affine01753 :=
  IntegerWeightedBernstein.checked 88 49 0 affine01753 bernsteinRow49 bernsteinWeights49 bernsteinWeights49_identity bernsteinRow49_weighted
theorem bernsteinRow49_positive : NestedInteger.bernsteinCheck 2 ![4,4] bernsteinRow49=true := by decide +kernel
#print axioms bernsteinRow49_weighted
#print axioms bernsteinRow49_identity
#print axioms bernsteinRow49_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
