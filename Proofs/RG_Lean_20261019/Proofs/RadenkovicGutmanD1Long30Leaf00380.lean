/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00380 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 186931421103530095306728275968000000000000 522765673610544346368113324991860178944 806054679595675083239063552000000000000))
theorem leaf00380_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 186931421103530095306728275968000000000000 522765673610544346368113324991860178944 806054679595675083239063552000000000000 raw00380=true := by decide +kernel
#print axioms leaf00380_raw
theorem leaf00380_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00380=true := by decide +kernel
#print axioms leaf00380_rectangular
def affine00380 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00380 (IntegerComputedClassCell.leftNumerator ![(3/320),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/320),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/320),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00380_transform : affine00380=(NestedInteger.clearedAll 3 raw00380 (IntegerComputedClassCell.leftNumerator ![(3/320),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/320),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/320),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00380_transform
theorem leaf00380_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00380=true := by decide +kernel
#print axioms leaf00380_sign
theorem leaf00380_log : RationalLog.accepts (3642947/2147483648) (-3424838723/1073741824) 10 8=true := by decide +kernel
#print axioms leaf00380_log
def leaf00380 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (162137162293/250000000000) (3642947/2147483648) (-3424838723/1073741824) 10 8 ![60,0,4] ![(3/320),0,0] ![(1/6400),1,(1/16)] affine00380
theorem leaf00380_checked : FastNestedCellData.accepts 1 2 4 leaf00380=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (162137162293/250000000000) (3642947/2147483648) (-3424838723/1073741824) 10 8 ![60,0,4] ![(3/320),0,0] ![(1/6400),1,(1/16)] 186931421103530095306728275968000000000000 522765673610544346368113324991860178944 806054679595675083239063552000000000000 raw00380 affine00380
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00380_raw leaf00380_rectangular
    leaf00380_transform leaf00380_sign leaf00380_log
#print axioms leaf00380_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
