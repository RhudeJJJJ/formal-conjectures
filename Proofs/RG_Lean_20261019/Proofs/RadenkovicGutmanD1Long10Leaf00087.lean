/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00087 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 62314767154534813311858376704000000000000 62282668304029745655802652427622023168 288081906307763367311310848000000000000))
theorem leaf00087_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 62314767154534813311858376704000000000000 62282668304029745655802652427622023168 288081906307763367311310848000000000000 raw00087=true := by decide +kernel
#print axioms leaf00087_raw
theorem leaf00087_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00087=true := by decide +kernel
#print axioms leaf00087_rectangular
def affine00087 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00087 (IntegerComputedClassCell.leftNumerator ![(3/320),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/320),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/320),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00087_transform : affine00087=(NestedInteger.clearedAll 3 raw00087 (IntegerComputedClassCell.leftNumerator ![(3/320),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/320),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/320),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00087_transform
theorem leaf00087_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00087=true := by decide +kernel
#print axioms leaf00087_sign
theorem leaf00087_log : RationalLog.accepts (882413/1073741824) (-15255724089/4294967296) 11 8=true := by decide +kernel
#print axioms leaf00087_log
def leaf00087 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (108098889483/500000000000) (882413/1073741824) (-15255724089/4294967296) 11 8 ![52,0,4] ![(3/320),0,0] ![(1/3200),1,(1/4)] affine00087
theorem leaf00087_checked : FastNestedCellData.accepts 1 0 4 leaf00087=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (108098889483/500000000000) (882413/1073741824) (-15255724089/4294967296) 11 8 ![52,0,4] ![(3/320),0,0] ![(1/3200),1,(1/4)] 62314767154534813311858376704000000000000 62282668304029745655802652427622023168 288081906307763367311310848000000000000 raw00087 affine00087
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00087_raw leaf00087_rectangular
    leaf00087_transform leaf00087_sign leaf00087_log
#print axioms leaf00087_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
