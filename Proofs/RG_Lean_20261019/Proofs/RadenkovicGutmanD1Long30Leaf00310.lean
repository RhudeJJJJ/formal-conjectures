/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00310 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4108389304917716744653091792486400000000 6143723654379288710518402541917569024 11034173200312150339354624000000000000))
theorem leaf00310_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4108389304917716744653091792486400000000 6143723654379288710518402541917569024 11034173200312150339354624000000000000 raw00310=true := by decide +kernel
#print axioms leaf00310_raw
theorem leaf00310_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00310=true := by decide +kernel
#print axioms leaf00310_rectangular
def affine00310 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00310 (IntegerComputedClassCell.leftNumerator ![(23/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/3200),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00310_transform : affine00310=(NestedInteger.clearedAll 3 raw00310 (IntegerComputedClassCell.leftNumerator ![(23/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/3200),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00310_transform
theorem leaf00310_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00310=true := by decide +kernel
#print axioms leaf00310_sign
theorem leaf00310_log : RationalLog.accepts (4125625/4294967296) (-14920677469/4294967296) 11 8=true := by decide +kernel
#print axioms leaf00310_log
def leaf00310 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (278395288113/500000000000) (4125625/4294967296) (-14920677469/4294967296) 11 8 ![60,0,4] ![(23/3200),0,0] ![(1/6400),1,(1/16)] affine00310
theorem leaf00310_checked : FastNestedCellData.accepts 1 2 4 leaf00310=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (278395288113/500000000000) (4125625/4294967296) (-14920677469/4294967296) 11 8 ![60,0,4] ![(23/3200),0,0] ![(1/6400),1,(1/16)] 4108389304917716744653091792486400000000 6143723654379288710518402541917569024 11034173200312150339354624000000000000 raw00310 affine00310
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00310_raw leaf00310_rectangular
    leaf00310_transform leaf00310_sign leaf00310_log
#print axioms leaf00310_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
