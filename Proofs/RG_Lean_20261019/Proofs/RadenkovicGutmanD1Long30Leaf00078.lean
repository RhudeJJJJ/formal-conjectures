/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00078 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 69153273727647336772810047488000000000000 66741219150389043012078633151165907337216 4450831184375205508296084553728000000000000))
theorem leaf00078_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 69153273727647336772810047488000000000000 66741219150389043012078633151165907337216 4450831184375205508296084553728000000000000 raw00078=true := by decide +kernel
#print axioms leaf00078_raw
theorem leaf00078_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00078=true := by decide +kernel
#print axioms leaf00078_rectangular
def affine00078 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00078 (IntegerComputedClassCell.leftNumerator ![(31/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/16000),0,(1/4)] ![(1/16000),1,(1/4)]))
theorem leaf00078_transform : affine00078=(NestedInteger.clearedAll 3 raw00078 (IntegerComputedClassCell.leftNumerator ![(31/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/16000),0,(1/4)] ![(1/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00078_transform
theorem leaf00078_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00078=true := by decide +kernel
#print axioms leaf00078_sign
theorem leaf00078_log : RationalLog.accepts (4083920251/4294967296) (-108204367/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00078_log
def leaf00078 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (7497612961/500000000000) (4083920251/4294967296) (-108204367/4294967296) 1 8 ![60,0,4] ![(31/16000),0,(1/4)] ![(1/16000),1,(1/4)] affine00078
theorem leaf00078_checked : FastNestedCellData.accepts 1 2 4 leaf00078=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (7497612961/500000000000) (4083920251/4294967296) (-108204367/4294967296) 1 8 ![60,0,4] ![(31/16000),0,(1/4)] ![(1/16000),1,(1/4)] 69153273727647336772810047488000000000000 66741219150389043012078633151165907337216 4450831184375205508296084553728000000000000 raw00078 affine00078
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00078_raw leaf00078_rectangular
    leaf00078_transform leaf00078_sign leaf00078_log
#print axioms leaf00078_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
