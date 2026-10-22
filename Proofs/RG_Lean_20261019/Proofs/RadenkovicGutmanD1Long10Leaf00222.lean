/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00222 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 58681966331365313986703654912000000000000 2203047760265958550190499679552998998016 3606930284941990250481188864000000000000))
theorem leaf00222_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 58681966331365313986703654912000000000000 2203047760265958550190499679552998998016 3606930284941990250481188864000000000000 raw00222=true := by decide +kernel
#print axioms leaf00222_raw
theorem leaf00222_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00222=true := by decide +kernel
#print axioms leaf00222_rectangular
def affine00222 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00222 (IntegerComputedClassCell.leftNumerator ![(127/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(127/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(127/3200),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00222_transform : affine00222=(NestedInteger.clearedAll 3 raw00222 (IntegerComputedClassCell.leftNumerator ![(127/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(127/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(127/3200),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00222_transform
theorem leaf00222_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00222=true := by decide +kernel
#print axioms leaf00222_sign
theorem leaf00222_log : RationalLog.accepts (12512739/536870912) (-8072413649/4294967296) 6 8=true := by decide +kernel
#print axioms leaf00222_log
def leaf00222 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (610781907669/1000000000000) (12512739/536870912) (-8072413649/4294967296) 6 8 ![52,0,4] ![(127/3200),0,0] ![(3/3200),1,(1/4)] affine00222
theorem leaf00222_checked : FastNestedCellData.accepts 1 0 4 leaf00222=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (610781907669/1000000000000) (12512739/536870912) (-8072413649/4294967296) 6 8 ![52,0,4] ![(127/3200),0,0] ![(3/3200),1,(1/4)] 58681966331365313986703654912000000000000 2203047760265958550190499679552998998016 3606930284941990250481188864000000000000 raw00222 affine00222
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00222_raw leaf00222_rectangular
    leaf00222_transform leaf00222_sign leaf00222_log
#print axioms leaf00222_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
