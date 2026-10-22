/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00450 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3292507671499548449976187092992000000000000 14816495535045955651095279675695154855936 20752882640951691583508447232000000000000))
theorem leaf00450_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3292507671499548449976187092992000000000000 14816495535045955651095279675695154855936 20752882640951691583508447232000000000000 raw00450=true := by decide +kernel
#print axioms leaf00450_raw
theorem leaf00450_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00450=true := by decide +kernel
#print axioms leaf00450_rectangular
def affine00450 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00450 (IntegerComputedClassCell.leftNumerator ![(37/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/3200),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00450_transform : affine00450=(NestedInteger.clearedAll 3 raw00450 (IntegerComputedClassCell.leftNumerator ![(37/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/3200),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00450_transform
theorem leaf00450_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00450=true := by decide +kernel
#print axioms leaf00450_sign
theorem leaf00450_log : RationalLog.accepts (5638333/2147483648) (-12761343695/4294967296) 9 8=true := by decide +kernel
#print axioms leaf00450_log
def leaf00450 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (713948794073/1000000000000) (5638333/2147483648) (-12761343695/4294967296) 9 8 ![60,0,4] ![(37/3200),0,0] ![(1/6400),1,(1/16)] affine00450
theorem leaf00450_checked : FastNestedCellData.accepts 1 2 4 leaf00450=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (713948794073/1000000000000) (5638333/2147483648) (-12761343695/4294967296) 9 8 ![60,0,4] ![(37/3200),0,0] ![(1/6400),1,(1/16)] 3292507671499548449976187092992000000000000 14816495535045955651095279675695154855936 20752882640951691583508447232000000000000 raw00450 affine00450
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00450_raw leaf00450_rectangular
    leaf00450_transform leaf00450_sign leaf00450_log
#print axioms leaf00450_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
