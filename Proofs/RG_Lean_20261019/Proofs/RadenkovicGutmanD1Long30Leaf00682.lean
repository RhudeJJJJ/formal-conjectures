/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00682 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 337098474007979755432531774668800000000000 160109724199339371051547634126895292874752 438077199060165331514118111232000000000000))
theorem leaf00682_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 337098474007979755432531774668800000000000 160109724199339371051547634126895292874752 438077199060165331514118111232000000000000 raw00682=true := by decide +kernel
#print axioms leaf00682_raw
theorem leaf00682_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00682=true := by decide +kernel
#print axioms leaf00682_rectangular
def affine00682 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00682 (IntegerComputedClassCell.leftNumerator ![(173/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(173/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(173/6400),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00682_transform : affine00682=(NestedInteger.clearedAll 3 raw00682 (IntegerComputedClassCell.leftNumerator ![(173/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(173/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(173/6400),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00682_transform
theorem leaf00682_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00682=true := by decide +kernel
#print axioms leaf00682_sign
theorem leaf00682_log : RationalLog.accepts (746972345/2147483648) (-2267794077/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00682_log
def leaf00682 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (365482897861/1000000000000) (746972345/2147483648) (-2267794077/4294967296) 2 8 ![60,0,4] ![(173/6400),0,(1/8)] ![(3/6400),1,(1/8)] affine00682
theorem leaf00682_checked : FastNestedCellData.accepts 1 2 4 leaf00682=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (365482897861/1000000000000) (746972345/2147483648) (-2267794077/4294967296) 2 8 ![60,0,4] ![(173/6400),0,(1/8)] ![(3/6400),1,(1/8)] 337098474007979755432531774668800000000000 160109724199339371051547634126895292874752 438077199060165331514118111232000000000000 raw00682 affine00682
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00682_raw leaf00682_rectangular
    leaf00682_transform leaf00682_sign leaf00682_log
#print axioms leaf00682_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
