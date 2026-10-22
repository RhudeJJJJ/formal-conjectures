/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00206 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 35073796831071111450455965696000000000000 27099971012795448808548486783321975554048 222702859241030087910644252672000000000000))
theorem leaf00206_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 35073796831071111450455965696000000000000 27099971012795448808548486783321975554048 222702859241030087910644252672000000000000 raw00206=true := by decide +kernel
#print axioms leaf00206_raw
theorem leaf00206_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00206=true := by decide +kernel
#print axioms leaf00206_rectangular
def affine00206 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00206 (IntegerComputedClassCell.leftNumerator ![(109/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(109/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(109/3200),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00206_transform : affine00206=(NestedInteger.clearedAll 3 raw00206 (IntegerComputedClassCell.leftNumerator ![(109/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(109/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(109/3200),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00206_transform
theorem leaf00206_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00206=true := by decide +kernel
#print axioms leaf00206_sign
theorem leaf00206_log : RationalLog.accepts (369814859/536870912) (-800485687/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00206_log
def leaf00206 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (121686677509/1000000000000) (369814859/536870912) (-800485687/4294967296) 1 8 ![52,0,4] ![(109/3200),0,(1/2)] ![(3/3200),1,(1/2)] affine00206
theorem leaf00206_checked : FastNestedCellData.accepts 1 0 4 leaf00206=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (121686677509/1000000000000) (369814859/536870912) (-800485687/4294967296) 1 8 ![52,0,4] ![(109/3200),0,(1/2)] ![(3/3200),1,(1/2)] 35073796831071111450455965696000000000000 27099971012795448808548486783321975554048 222702859241030087910644252672000000000000 raw00206 affine00206
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00206_raw leaf00206_rectangular
    leaf00206_transform leaf00206_sign leaf00206_log
#print axioms leaf00206_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
