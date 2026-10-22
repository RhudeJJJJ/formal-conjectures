/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00999 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 76534476414369489333936508108800000000000 53242813342754511541047303426817048707072 160410803978806425950447730688000000000000))
theorem leaf00999_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 76534476414369489333936508108800000000000 53242813342754511541047303426817048707072 160410803978806425950447730688000000000000 raw00999=true := by decide +kernel
#print axioms leaf00999_raw
theorem leaf00999_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00999=true := by decide +kernel
#print axioms leaf00999_rectangular
def affine00999 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00999 (IntegerComputedClassCell.leftNumerator ![(23/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/160),0,(1/2)] ![(1/160),1,(1/2)]))
theorem leaf00999_transform : affine00999=(NestedInteger.clearedAll 3 raw00999 (IntegerComputedClassCell.leftNumerator ![(23/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/160),0,(1/2)] ![(1/160),1,(1/2)])) := by decide +kernel
#print axioms leaf00999_transform
theorem leaf00999_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00999=true := by decide +kernel
#print axioms leaf00999_sign
theorem leaf00999_log : RationalLog.accepts (1121649355/2147483648) (-174347899/536870912) 1 8=true := by decide +kernel
#print axioms leaf00999_log
def leaf00999 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (165957691197/500000000000) (1121649355/2147483648) (-174347899/536870912) 1 8 ![60,0,4] ![(23/160),0,(1/2)] ![(1/160),1,(1/2)] affine00999
theorem leaf00999_checked : FastNestedCellData.accepts 1 2 4 leaf00999=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (165957691197/500000000000) (1121649355/2147483648) (-174347899/536870912) 1 8 ![60,0,4] ![(23/160),0,(1/2)] ![(1/160),1,(1/2)] 76534476414369489333936508108800000000000 53242813342754511541047303426817048707072 160410803978806425950447730688000000000000 raw00999 affine00999
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00999_raw leaf00999_rectangular
    leaf00999_transform leaf00999_sign leaf00999_log
#print axioms leaf00999_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
