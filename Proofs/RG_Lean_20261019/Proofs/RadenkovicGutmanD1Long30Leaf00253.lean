/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00253 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 50388743906275850376581847449600000000000 45805263654943713327895159354418867994624 1117918950897944595377407655936000000000000))
theorem leaf00253_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 50388743906275850376581847449600000000000 45805263654943713327895159354418867994624 1117918950897944595377407655936000000000000 raw00253=true := by decide +kernel
#print axioms leaf00253_raw
theorem leaf00253_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00253=true := by decide +kernel
#print axioms leaf00253_rectangular
def affine00253 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00253 (IntegerComputedClassCell.leftNumerator ![(17/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/3200),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00253_transform : affine00253=(NestedInteger.clearedAll 3 raw00253 (IntegerComputedClassCell.leftNumerator ![(17/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/3200),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00253_transform
theorem leaf00253_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00253=true := by decide +kernel
#print axioms leaf00253_sign
theorem leaf00253_log : RationalLog.accepts (3750610485/4294967296) (-291038441/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00253_log
def leaf00253 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (40973689209/1000000000000) (3750610485/4294967296) (-291038441/4294967296) 1 8 ![60,0,4] ![(17/3200),0,(1/4)] ![(1/6400),1,(1/4)] affine00253
theorem leaf00253_checked : FastNestedCellData.accepts 1 2 4 leaf00253=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (40973689209/1000000000000) (3750610485/4294967296) (-291038441/4294967296) 1 8 ![60,0,4] ![(17/3200),0,(1/4)] ![(1/6400),1,(1/4)] 50388743906275850376581847449600000000000 45805263654943713327895159354418867994624 1117918950897944595377407655936000000000000 raw00253 affine00253
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00253_raw leaf00253_rectangular
    leaf00253_transform leaf00253_sign leaf00253_log
#print axioms leaf00253_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
