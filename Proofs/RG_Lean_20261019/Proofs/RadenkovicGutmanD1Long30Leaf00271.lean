/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00271 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2665499906892261765693413785600000000000 1760747748351897036372993813386631315456 9519808732753779128713347072000000000000))
theorem leaf00271_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2665499906892261765693413785600000000000 1760747748351897036372993813386631315456 9519808732753779128713347072000000000000 raw00271=true := by decide +kernel
#print axioms leaf00271_raw
theorem leaf00271_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00271=true := by decide +kernel
#print axioms leaf00271_rectangular
def affine00271 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00271 (IntegerComputedClassCell.leftNumerator ![(19/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/3200),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00271_transform : affine00271=(NestedInteger.clearedAll 3 raw00271 (IntegerComputedClassCell.leftNumerator ![(19/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/3200),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00271_transform
theorem leaf00271_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00271=true := by decide +kernel
#print axioms leaf00271_sign
theorem leaf00271_log : RationalLog.accepts (598571505/1073741824) (-313725287/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00271_log
def leaf00271 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (46239052637/250000000000) (598571505/1073741824) (-313725287/1073741824) 1 8 ![60,0,4] ![(19/3200),0,(1/16)] ![(1/6400),1,(1/16)] affine00271
theorem leaf00271_checked : FastNestedCellData.accepts 1 2 4 leaf00271=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (46239052637/250000000000) (598571505/1073741824) (-313725287/1073741824) 1 8 ![60,0,4] ![(19/3200),0,(1/16)] ![(1/6400),1,(1/16)] 2665499906892261765693413785600000000000 1760747748351897036372993813386631315456 9519808732753779128713347072000000000000 raw00271 affine00271
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00271_raw leaf00271_rectangular
    leaf00271_transform leaf00271_sign leaf00271_log
#print axioms leaf00271_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
