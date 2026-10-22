/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00019 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 16845422738655952967093452800000000000 16083003163112460854442726112710623232 859953569300224963298459648000000000000))
theorem leaf00019_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 16845422738655952967093452800000000000 16083003163112460854442726112710623232 859953569300224963298459648000000000000 raw00019=true := by decide +kernel
#print axioms leaf00019_raw
theorem leaf00019_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00019=true := by decide +kernel
#print axioms leaf00019_rectangular
def affine00019 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00019 (IntegerComputedClassCell.leftNumerator ![(19/8000),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/8000),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/8000),0,(1/4)] ![(3/16000),1,(1/4)]))
theorem leaf00019_transform : affine00019=(NestedInteger.clearedAll 3 raw00019 (IntegerComputedClassCell.leftNumerator ![(19/8000),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/8000),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/8000),0,(1/4)] ![(3/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00019_transform
theorem leaf00019_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00019=true := by decide +kernel
#print axioms leaf00019_sign
theorem leaf00019_log : RationalLog.accepts (503162045/536870912) (-139254479/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00019_log
def leaf00019 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (2337772023/125000000000) (503162045/536870912) (-139254479/4294967296) 1 8 ![52,0,4] ![(19/8000),0,(1/4)] ![(3/16000),1,(1/4)] affine00019
theorem leaf00019_checked : FastNestedCellData.accepts 1 0 4 leaf00019=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (2337772023/125000000000) (503162045/536870912) (-139254479/4294967296) 1 8 ![52,0,4] ![(19/8000),0,(1/4)] ![(3/16000),1,(1/4)] 16845422738655952967093452800000000000 16083003163112460854442726112710623232 859953569300224963298459648000000000000 raw00019 affine00019
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00019_raw leaf00019_rectangular
    leaf00019_transform leaf00019_sign leaf00019_log
#print axioms leaf00019_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
