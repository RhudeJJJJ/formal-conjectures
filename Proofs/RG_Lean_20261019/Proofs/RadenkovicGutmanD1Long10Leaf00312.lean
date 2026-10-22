/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00312 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 8147616856595170046873121587200000000000 1706382735224661846620011351548903817216 2414602190010804095431789772800000000000))
theorem leaf00312_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 8147616856595170046873121587200000000000 1706382735224661846620011351548903817216 2414602190010804095431789772800000000000 raw00312=true := by decide +kernel
#print axioms leaf00312_raw
theorem leaf00312_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00312=true := by decide +kernel
#print axioms leaf00312_rectangular
def affine00312 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00312 (IntegerComputedClassCell.leftNumerator ![(3/32),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/32),0,0] ![(1/320),1,(1/4)]))
theorem leaf00312_transform : affine00312=(NestedInteger.clearedAll 3 raw00312 (IntegerComputedClassCell.leftNumerator ![(3/32),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/32),0,0] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00312_transform
theorem leaf00312_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00312=true := by decide +kernel
#print axioms leaf00312_sign
theorem leaf00312_log : RationalLog.accepts (527048129/4294967296) (-2252610935/2147483648) 4 8=true := by decide +kernel
#print axioms leaf00312_log
def leaf00312 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (17667327793/25000000000) (527048129/4294967296) (-2252610935/2147483648) 4 8 ![52,0,4] ![(3/32),0,0] ![(1/320),1,(1/4)] affine00312
theorem leaf00312_checked : FastNestedCellData.accepts 1 0 4 leaf00312=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (17667327793/25000000000) (527048129/4294967296) (-2252610935/2147483648) 4 8 ![52,0,4] ![(3/32),0,0] ![(1/320),1,(1/4)] 8147616856595170046873121587200000000000 1706382735224661846620011351548903817216 2414602190010804095431789772800000000000 raw00312 affine00312
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00312_raw leaf00312_rectangular
    leaf00312_transform leaf00312_sign leaf00312_log
#print axioms leaf00312_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
