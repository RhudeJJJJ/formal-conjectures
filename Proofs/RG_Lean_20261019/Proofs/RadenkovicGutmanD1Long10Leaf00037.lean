/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00037 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 443187391994618284245988147200000000000 410450536799445725318681769971363610624 13346985355442245792824295424000000000000))
theorem leaf00037_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 443187391994618284245988147200000000000 410450536799445725318681769971363610624 13346985355442245792824295424000000000000 raw00037=true := by decide +kernel
#print axioms leaf00037_raw
theorem leaf00037_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00037=true := by decide +kernel
#print axioms leaf00037_rectangular
def affine00037 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00037 (IntegerComputedClassCell.leftNumerator ![(31/8000),0,(1/4)] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/8000),0,(1/4)] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/8000),0,(1/4)] ![(3/8000),1,(1/4)]))
theorem leaf00037_transform : affine00037=(NestedInteger.clearedAll 3 raw00037 (IntegerComputedClassCell.leftNumerator ![(31/8000),0,(1/4)] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/8000),0,(1/4)] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/8000),0,(1/4)] ![(3/8000),1,(1/4)])) := by decide +kernel
#print axioms leaf00037_transform
theorem leaf00037_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00037=true := by decide +kernel
#print axioms leaf00037_sign
theorem leaf00037_log : RationalLog.accepts (482379665/536870912) (-7182407/134217728) 1 8=true := by decide +kernel
#print axioms leaf00037_log
def leaf00037 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (15376151463/500000000000) (482379665/536870912) (-7182407/134217728) 1 8 ![52,0,4] ![(31/8000),0,(1/4)] ![(3/8000),1,(1/4)] affine00037
theorem leaf00037_checked : FastNestedCellData.accepts 1 0 4 leaf00037=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (15376151463/500000000000) (482379665/536870912) (-7182407/134217728) 1 8 ![52,0,4] ![(31/8000),0,(1/4)] ![(3/8000),1,(1/4)] 443187391994618284245988147200000000000 410450536799445725318681769971363610624 13346985355442245792824295424000000000000 raw00037 affine00037
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00037_raw leaf00037_rectangular
    leaf00037_transform leaf00037_sign leaf00037_log
#print axioms leaf00037_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
