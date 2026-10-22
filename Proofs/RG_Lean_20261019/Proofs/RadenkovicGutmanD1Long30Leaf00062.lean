/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00062 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7986713661494966184403009536000000000000 7484055043228763388843631151287520722944 270090063532610264715206066176000000000000))
theorem leaf00062_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7986713661494966184403009536000000000000 7484055043228763388843631151287520722944 270090063532610264715206066176000000000000 raw00062=true := by decide +kernel
#print axioms leaf00062_raw
theorem leaf00062_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00062=true := by decide +kernel
#print axioms leaf00062_rectangular
def affine00062 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00062 (IntegerComputedClassCell.leftNumerator ![(7/4000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/4000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/4000),0,(1/8)] ![(1/16000),1,(1/8)]))
theorem leaf00062_transform : affine00062=(NestedInteger.clearedAll 3 raw00062 (IntegerComputedClassCell.leftNumerator ![(7/4000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/4000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/4000),0,(1/8)] ![(1/16000),1,(1/8)])) := by decide +kernel
#print axioms leaf00062_transform
theorem leaf00062_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00062=true := by decide +kernel
#print axioms leaf00062_sign
theorem leaf00062_log : RationalLog.accepts (489517667/536870912) (-99146251/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00062_log
def leaf00062 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (27709479369/1000000000000) (489517667/536870912) (-99146251/2147483648) 1 8 ![60,0,4] ![(7/4000),0,(1/8)] ![(1/16000),1,(1/8)] affine00062
theorem leaf00062_checked : FastNestedCellData.accepts 1 2 4 leaf00062=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (27709479369/1000000000000) (489517667/536870912) (-99146251/2147483648) 1 8 ![60,0,4] ![(7/4000),0,(1/8)] ![(1/16000),1,(1/8)] 7986713661494966184403009536000000000000 7484055043228763388843631151287520722944 270090063532610264715206066176000000000000 raw00062 affine00062
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00062_raw leaf00062_rectangular
    leaf00062_transform leaf00062_sign leaf00062_log
#print axioms leaf00062_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
