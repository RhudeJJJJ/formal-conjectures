/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00421 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5632922364811758526401609728000000000000 2845454109971896033989858480849753735168 9099920247026179580104802304000000000000))
theorem leaf00421_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5632922364811758526401609728000000000000 2845454109971896033989858480849753735168 9099920247026179580104802304000000000000 raw00421=true := by decide +kernel
#print axioms leaf00421_raw
theorem leaf00421_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00421=true := by decide +kernel
#print axioms leaf00421_rectangular
def affine00421 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00421 (IntegerComputedClassCell.leftNumerator ![(17/1600),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/1600),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/1600),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00421_transform : affine00421=(NestedInteger.clearedAll 3 raw00421 (IntegerComputedClassCell.leftNumerator ![(17/1600),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/1600),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/1600),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00421_transform
theorem leaf00421_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00421=true := by decide +kernel
#print axioms leaf00421_sign
theorem leaf00421_log : RationalLog.accepts (51649429/134217728) (-2050812975/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00421_log
def leaf00421 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (312690005267/1000000000000) (51649429/134217728) (-2050812975/4294967296) 2 8 ![60,0,4] ![(17/1600),0,(1/16)] ![(1/6400),1,(1/16)] affine00421
theorem leaf00421_checked : FastNestedCellData.accepts 1 2 4 leaf00421=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (312690005267/1000000000000) (51649429/134217728) (-2050812975/4294967296) 2 8 ![60,0,4] ![(17/1600),0,(1/16)] ![(1/6400),1,(1/16)] 5632922364811758526401609728000000000000 2845454109971896033989858480849753735168 9099920247026179580104802304000000000000 raw00421 affine00421
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00421_raw leaf00421_rectangular
    leaf00421_transform leaf00421_sign leaf00421_log
#print axioms leaf00421_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
