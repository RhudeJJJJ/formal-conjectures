/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00163 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2985351376893016102026575085568000000000000 2108118470757176572327350054990056685305856 13026246159200839766176664911872000000000000))
theorem leaf00163_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2985351376893016102026575085568000000000000 2108118470757176572327350054990056685305856 13026246159200839766176664911872000000000000 raw00163=true := by decide +kernel
#print axioms leaf00163_raw
theorem leaf00163_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00163=true := by decide +kernel
#print axioms leaf00163_rectangular
def affine00163 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00163 (IntegerComputedClassCell.leftNumerator ![(7/320),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/320),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/320),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00163_transform : affine00163=(NestedInteger.clearedAll 3 raw00163 (IntegerComputedClassCell.leftNumerator ![(7/320),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/320),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/320),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00163_transform
theorem leaf00163_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00163=true := by decide +kernel
#print axioms leaf00163_sign
theorem leaf00163_log : RationalLog.accepts (2610444759/4294967296) (-1069282241/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00163_log
def leaf00163 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (161836222423/1000000000000) (2610444759/4294967296) (-1069282241/4294967296) 1 8 ![52,0,4] ![(7/320),0,(1/4)] ![(3/6400),1,(1/4)] affine00163
theorem leaf00163_checked : FastNestedCellData.accepts 1 0 4 leaf00163=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (161836222423/1000000000000) (2610444759/4294967296) (-1069282241/4294967296) 1 8 ![52,0,4] ![(7/320),0,(1/4)] ![(3/6400),1,(1/4)] 2985351376893016102026575085568000000000000 2108118470757176572327350054990056685305856 13026246159200839766176664911872000000000000 raw00163 affine00163
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00163_raw leaf00163_rectangular
    leaf00163_transform leaf00163_sign leaf00163_log
#print axioms leaf00163_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
