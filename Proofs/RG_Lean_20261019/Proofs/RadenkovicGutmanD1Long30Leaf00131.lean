/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00131 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 394314052903925356574267146240000000000 318236598920219630869404939085598949376 3402902723674928438807803985920000000000))
theorem leaf00131_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 394314052903925356574267146240000000000 318236598920219630869404939085598949376 3402902723674928438807803985920000000000 raw00131=true := by decide +kernel
#print axioms leaf00131_raw
theorem leaf00131_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00131=true := by decide +kernel
#print axioms leaf00131_rectangular
def affine00131 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00131 (IntegerComputedClassCell.leftNumerator ![(47/16000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(47/16000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(47/16000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00131_transform : affine00131=(NestedInteger.clearedAll 3 raw00131 (IntegerComputedClassCell.leftNumerator ![(47/16000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(47/16000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(47/16000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00131_transform
theorem leaf00131_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00131=true := by decide +kernel
#print axioms leaf00131_sign
theorem leaf00131_log : RationalLog.accepts (3169869143/4294967296) (-652305997/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00131_log
def leaf00131 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (3740766337/40000000000) (3169869143/4294967296) (-652305997/4294967296) 1 8 ![60,0,4] ![(47/16000),0,(1/16)] ![(3/32000),1,(1/16)] affine00131
theorem leaf00131_checked : FastNestedCellData.accepts 1 2 4 leaf00131=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (3740766337/40000000000) (3169869143/4294967296) (-652305997/4294967296) 1 8 ![60,0,4] ![(47/16000),0,(1/16)] ![(3/32000),1,(1/16)] 394314052903925356574267146240000000000 318236598920219630869404939085598949376 3402902723674928438807803985920000000000 raw00131 affine00131
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00131_raw leaf00131_rectangular
    leaf00131_transform leaf00131_sign leaf00131_log
#print axioms leaf00131_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
