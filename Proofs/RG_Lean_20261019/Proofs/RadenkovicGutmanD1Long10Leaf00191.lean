/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00191 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 30550337518294213188906909696000000000000 24264876303729022565277062211099313569792 228929530487526936228122329088000000000000))
theorem leaf00191_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 30550337518294213188906909696000000000000 24264876303729022565277062211099313569792 228929530487526936228122329088000000000000 raw00191=true := by decide +kernel
#print axioms leaf00191_raw
theorem leaf00191_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00191=true := by decide +kernel
#print axioms leaf00191_rectangular
def affine00191 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00191 (IntegerComputedClassCell.leftNumerator ![(47/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(47/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(47/1600),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00191_transform : affine00191=(NestedInteger.clearedAll 3 raw00191 (IntegerComputedClassCell.leftNumerator ![(47/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(47/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(47/1600),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00191_transform
theorem leaf00191_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00191=true := by decide +kernel
#print axioms leaf00191_sign
theorem leaf00191_log : RationalLog.accepts (3084392513/4294967296) (-44438045/268435456) 1 8=true := by decide +kernel
#print axioms leaf00191_log
def leaf00191 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (13249096923/125000000000) (3084392513/4294967296) (-44438045/268435456) 1 8 ![52,0,4] ![(47/1600),0,(1/2)] ![(3/3200),1,(1/2)] affine00191
theorem leaf00191_checked : FastNestedCellData.accepts 1 0 4 leaf00191=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (13249096923/125000000000) (3084392513/4294967296) (-44438045/268435456) 1 8 ![52,0,4] ![(47/1600),0,(1/2)] ![(3/3200),1,(1/2)] 30550337518294213188906909696000000000000 24264876303729022565277062211099313569792 228929530487526936228122329088000000000000 raw00191 affine00191
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00191_raw leaf00191_rectangular
    leaf00191_transform leaf00191_sign leaf00191_log
#print axioms leaf00191_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
