/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00229 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 5103184275243161389656702976000000000000 2941658697366572734759713127785190916096 10384146288881578567547224064000000000000))
theorem leaf00229_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 5103184275243161389656702976000000000000 2941658697366572734759713127785190916096 10384146288881578567547224064000000000000 raw00229=true := by decide +kernel
#print axioms leaf00229_raw
theorem leaf00229_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00229=true := by decide +kernel
#print axioms leaf00229_rectangular
def affine00229 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00229 (IntegerComputedClassCell.leftNumerator ![(133/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(133/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(133/3200),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00229_transform : affine00229=(NestedInteger.clearedAll 3 raw00229 (IntegerComputedClassCell.leftNumerator ![(133/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(133/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(133/3200),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00229_transform
theorem leaf00229_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00229=true := by decide +kernel
#print axioms leaf00229_sign
theorem leaf00229_log : RationalLog.accepts (964624397/2147483648) (-1718659667/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00229_log
def leaf00229 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (17705227129/62500000000) (964624397/2147483648) (-1718659667/4294967296) 2 8 ![52,0,4] ![(133/3200),0,(1/4)] ![(3/3200),1,(1/4)] affine00229
theorem leaf00229_checked : FastNestedCellData.accepts 1 0 4 leaf00229=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (17705227129/62500000000) (964624397/2147483648) (-1718659667/4294967296) 2 8 ![52,0,4] ![(133/3200),0,(1/4)] ![(3/3200),1,(1/4)] 5103184275243161389656702976000000000000 2941658697366572734759713127785190916096 10384146288881578567547224064000000000000 raw00229 affine00229
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00229_raw leaf00229_rectangular
    leaf00229_transform leaf00229_sign leaf00229_log
#print axioms leaf00229_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
