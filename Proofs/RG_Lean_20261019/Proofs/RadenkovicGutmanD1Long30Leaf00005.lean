/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00005 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1196955620105853042995442483200000000000 10294234137016084746436103022575616 99155254469452783996108800000000000))
theorem leaf00005_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1196955620105853042995442483200000000000 10294234137016084746436103022575616 99155254469452783996108800000000000 raw00005=true := by decide +kernel
#print axioms leaf00005_raw
theorem leaf00005_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00005=true := by decide +kernel
#print axioms leaf00005_rectangular
def affine00005 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00005 (IntegerComputedClassCell.leftNumerator ![(17/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/16000),0,0] ![(1/16000),1,(1/16)]))
theorem leaf00005_transform : affine00005=(NestedInteger.clearedAll 3 raw00005 (IntegerComputedClassCell.leftNumerator ![(17/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/16000),0,0] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00005_transform
theorem leaf00005_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00005=true := by decide +kernel
#print axioms leaf00005_sign
theorem leaf00005_log : RationalLog.accepts (4183/536870912) (-12629871609/2147483648) 17 8=true := by decide +kernel
#print axioms leaf00005_log
def leaf00005 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (20763870139/200000000000) (4183/536870912) (-12629871609/2147483648) 17 8 ![60,0,4] ![(17/16000),0,0] ![(1/16000),1,(1/16)] affine00005
theorem leaf00005_checked : FastNestedCellData.accepts 1 2 4 leaf00005=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (20763870139/200000000000) (4183/536870912) (-12629871609/2147483648) 17 8 ![60,0,4] ![(17/16000),0,0] ![(1/16000),1,(1/16)] 1196955620105853042995442483200000000000 10294234137016084746436103022575616 99155254469452783996108800000000000 raw00005 affine00005
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00005_raw leaf00005_rectangular
    leaf00005_transform leaf00005_sign leaf00005_log
#print axioms leaf00005_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
