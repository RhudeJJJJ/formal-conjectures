/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00758 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 44308556737043687862760059699200000000000 27323963199871488006010422188367050440704 113756392296590337621559030579200000000000))
theorem leaf00758_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 44308556737043687862760059699200000000000 27323963199871488006010422188367050440704 113756392296590337621559030579200000000000 raw00758=true := by decide +kernel
#print axioms leaf00758_raw
theorem leaf00758_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00758=true := by decide +kernel
#print axioms leaf00758_rectangular
def affine00758 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00758 (IntegerComputedClassCell.leftNumerator ![(109/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(109/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(109/3200),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00758_transform : affine00758=(NestedInteger.clearedAll 3 raw00758 (IntegerComputedClassCell.leftNumerator ![(109/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(109/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(109/3200),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00758_transform
theorem leaf00758_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00758=true := by decide +kernel
#print axioms leaf00758_sign
theorem leaf00758_log : RationalLog.accepts (2135626071/4294967296) (-1500412743/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00758_log
def leaf00758 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (24019716737/100000000000) (2135626071/4294967296) (-1500412743/4294967296) 2 8 ![60,0,4] ![(109/3200),0,(1/4)] ![(3/3200),1,(1/4)] affine00758
theorem leaf00758_checked : FastNestedCellData.accepts 1 2 4 leaf00758=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (24019716737/100000000000) (2135626071/4294967296) (-1500412743/4294967296) 2 8 ![60,0,4] ![(109/3200),0,(1/4)] ![(3/3200),1,(1/4)] 44308556737043687862760059699200000000000 27323963199871488006010422188367050440704 113756392296590337621559030579200000000000 raw00758 affine00758
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00758_raw leaf00758_rectangular
    leaf00758_transform leaf00758_sign leaf00758_log
#print axioms leaf00758_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
