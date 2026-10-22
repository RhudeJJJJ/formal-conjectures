/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00048 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 223949451884395918842142916608000000000000 217548945093576266292008328099016948580352 17919533537051315649006538850304000000000000))
theorem leaf00048_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 223949451884395918842142916608000000000000 217548945093576266292008328099016948580352 17919533537051315649006538850304000000000000 raw00048=true := by decide +kernel
#print axioms leaf00048_raw
theorem leaf00048_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00048=true := by decide +kernel
#print axioms leaf00048_rectangular
def affine00048 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00048 (IntegerComputedClassCell.leftNumerator ![(1/640),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/640),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/640),0,(1/4)] ![(1/16000),1,(1/4)]))
theorem leaf00048_transform : affine00048=(NestedInteger.clearedAll 3 raw00048 (IntegerComputedClassCell.leftNumerator ![(1/640),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/640),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/640),0,(1/4)] ![(1/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00048_transform
theorem leaf00048_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00048=true := by decide +kernel
#print axioms leaf00048_sign
theorem leaf00048_log : RationalLog.accepts (4122172023/4294967296) (-44091859/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00048_log
def leaf00048 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (12140324113/1000000000000) (4122172023/4294967296) (-44091859/2147483648) 1 8 ![60,0,4] ![(1/640),0,(1/4)] ![(1/16000),1,(1/4)] affine00048
theorem leaf00048_checked : FastNestedCellData.accepts 1 2 4 leaf00048=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (12140324113/1000000000000) (4122172023/4294967296) (-44091859/2147483648) 1 8 ![60,0,4] ![(1/640),0,(1/4)] ![(1/16000),1,(1/4)] 223949451884395918842142916608000000000000 217548945093576266292008328099016948580352 17919533537051315649006538850304000000000000 raw00048 affine00048
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00048_raw leaf00048_rectangular
    leaf00048_transform leaf00048_sign leaf00048_log
#print axioms leaf00048_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
