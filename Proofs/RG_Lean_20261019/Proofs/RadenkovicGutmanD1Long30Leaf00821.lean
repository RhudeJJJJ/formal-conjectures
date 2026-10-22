/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00821 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 13023565443158880916501361065984000000000000 3273576208382369708944426055177386225303552 4636735061943772037657550389248000000000000))
theorem leaf00821_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 13023565443158880916501361065984000000000000 3273576208382369708944426055177386225303552 4636735061943772037657550389248000000000000 raw00821=true := by decide +kernel
#print axioms leaf00821_raw
theorem leaf00821_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00821=true := by decide +kernel
#print axioms leaf00821_rectangular
def affine00821 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00821 (IntegerComputedClassCell.leftNumerator ![(37/800),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/800),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/800),0,(1/16)] ![(3/3200),1,(1/16)]))
theorem leaf00821_transform : affine00821=(NestedInteger.clearedAll 3 raw00821 (IntegerComputedClassCell.leftNumerator ![(37/800),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/800),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/800),0,(1/16)] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00821_transform
theorem leaf00821_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00821=true := by decide +kernel
#print axioms leaf00821_sign
theorem leaf00821_log : RationalLog.accepts (632806787/4294967296) (-4112504475/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00821_log
def leaf00821 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (706008897349/1000000000000) (632806787/4294967296) (-4112504475/4294967296) 3 8 ![60,0,4] ![(37/800),0,(1/16)] ![(3/3200),1,(1/16)] affine00821
theorem leaf00821_checked : FastNestedCellData.accepts 1 2 4 leaf00821=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (706008897349/1000000000000) (632806787/4294967296) (-4112504475/4294967296) 3 8 ![60,0,4] ![(37/800),0,(1/16)] ![(3/3200),1,(1/16)] 13023565443158880916501361065984000000000000 3273576208382369708944426055177386225303552 4636735061943772037657550389248000000000000 raw00821 affine00821
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00821_raw leaf00821_rectangular
    leaf00821_transform leaf00821_sign leaf00821_log
#print axioms leaf00821_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
