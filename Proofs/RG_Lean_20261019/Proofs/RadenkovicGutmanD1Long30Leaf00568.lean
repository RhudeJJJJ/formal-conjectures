/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00568 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 153860498486485273123225600000000000 115607923447353760805988072683470848 881229476268332655050752000000000000))
theorem leaf00568_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 153860498486485273123225600000000000 115607923447353760805988072683470848 881229476268332655050752000000000000 raw00568=true := by decide +kernel
#print axioms leaf00568_raw
theorem leaf00568_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00568=true := by decide +kernel
#print axioms leaf00568_rectangular
def affine00568 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00568 (IntegerComputedClassCell.leftNumerator ![(7/400),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/400),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/400),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00568_transform : affine00568=(NestedInteger.clearedAll 3 raw00568 (IntegerComputedClassCell.leftNumerator ![(7/400),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/400),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/400),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00568_transform
theorem leaf00568_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00568=true := by decide +kernel
#print axioms leaf00568_sign
theorem leaf00568_log : RationalLog.accepts (2852889945/4294967296) (-878560173/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00568_log
def leaf00568 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (128114601/976562500) (2852889945/4294967296) (-878560173/4294967296) 1 8 ![60,0,4] ![(7/400),0,(1/4)] ![(1/3200),1,(1/4)] affine00568
theorem leaf00568_checked : FastNestedCellData.accepts 1 2 4 leaf00568=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (128114601/976562500) (2852889945/4294967296) (-878560173/4294967296) 1 8 ![60,0,4] ![(7/400),0,(1/4)] ![(1/3200),1,(1/4)] 153860498486485273123225600000000000 115607923447353760805988072683470848 881229476268332655050752000000000000 raw00568 affine00568
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00568_raw leaf00568_rectangular
    leaf00568_transform leaf00568_sign leaf00568_log
#print axioms leaf00568_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
