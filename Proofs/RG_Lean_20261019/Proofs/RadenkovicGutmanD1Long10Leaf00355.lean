/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00355 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 448517971664091571313559837081600000000000 313740339737158787091594572703311239053312 645179024962736236647422099456000000000000))
theorem leaf00355_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 448517971664091571313559837081600000000000 313740339737158787091594572703311239053312 645179024962736236647422099456000000000000 raw00355=true := by decide +kernel
#print axioms leaf00355_raw
theorem leaf00355_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00355=true := by decide +kernel
#print axioms leaf00355_rectangular
def affine00355 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00355 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/16),0,(1/4)] ![(1/80),1,(1/4)]))
theorem leaf00355_transform : affine00355=(NestedInteger.clearedAll 3 raw00355 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/16),0,(1/4)] ![(1/80),1,(1/4)])) := by decide +kernel
#print axioms leaf00355_transform
theorem leaf00355_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00355=true := by decide +kernel
#print axioms leaf00355_sign
theorem leaf00355_log : RationalLog.accepts (1010691305/2147483648) (-1618477329/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00355_log
def leaf00355 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (486284159277/1000000000000) (1010691305/2147483648) (-1618477329/4294967296) 2 8 ![52,0,4] ![(3/16),0,(1/4)] ![(1/80),1,(1/4)] affine00355
theorem leaf00355_checked : FastNestedCellData.accepts 1 0 4 leaf00355=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (486284159277/1000000000000) (1010691305/2147483648) (-1618477329/4294967296) 2 8 ![52,0,4] ![(3/16),0,(1/4)] ![(1/80),1,(1/4)] 448517971664091571313559837081600000000000 313740339737158787091594572703311239053312 645179024962736236647422099456000000000000 raw00355 affine00355
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00355_raw leaf00355_rectangular
    leaf00355_transform leaf00355_sign leaf00355_log
#print axioms leaf00355_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
