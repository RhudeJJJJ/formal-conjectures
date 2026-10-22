/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00726 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 569104886387422242909506764800000000000 152187486407705800371980607294101520384 240866498766841046406004736000000000000))
theorem leaf00726_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 569104886387422242909506764800000000000 152187486407705800371980607294101520384 240866498766841046406004736000000000000 raw00726=true := by decide +kernel
#print axioms leaf00726_raw
theorem leaf00726_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00726=true := by decide +kernel
#print axioms leaf00726_rectangular
def affine00726 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00726 (IntegerComputedClassCell.leftNumerator ![(1/32),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/32),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/32),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00726_transform : affine00726=(NestedInteger.clearedAll 3 raw00726 (IntegerComputedClassCell.leftNumerator ![(1/32),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/32),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/32),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00726_transform
theorem leaf00726_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00726=true := by decide +kernel
#print axioms leaf00726_sign
theorem leaf00726_log : RationalLog.accepts (21994835/134217728) (-1942029285/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00726_log
def leaf00726 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (315916674147/500000000000) (21994835/134217728) (-1942029285/2147483648) 3 8 ![60,0,4] ![(1/32),0,(1/16)] ![(3/6400),1,(1/16)] affine00726
theorem leaf00726_checked : FastNestedCellData.accepts 1 2 4 leaf00726=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (315916674147/500000000000) (21994835/134217728) (-1942029285/2147483648) 3 8 ![60,0,4] ![(1/32),0,(1/16)] ![(3/6400),1,(1/16)] 569104886387422242909506764800000000000 152187486407705800371980607294101520384 240866498766841046406004736000000000000 raw00726 affine00726
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00726_raw leaf00726_rectangular
    leaf00726_transform leaf00726_sign leaf00726_log
#print axioms leaf00726_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
