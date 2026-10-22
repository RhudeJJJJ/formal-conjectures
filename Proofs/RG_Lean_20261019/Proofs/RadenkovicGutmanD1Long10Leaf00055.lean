/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00055 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 57897021047372278798273740800000000000 51885651728803264988753308336611393536 1126503823400195533677422182400000000000))
theorem leaf00055_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 57897021047372278798273740800000000000 51885651728803264988753308336611393536 1126503823400195533677422182400000000000 raw00055=true := by decide +kernel
#print axioms leaf00055_raw
theorem leaf00055_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00055=true := by decide +kernel
#print axioms leaf00055_rectangular
def affine00055 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00055 (IntegerComputedClassCell.leftNumerator ![(19/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/3200),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00055_transform : affine00055=(NestedInteger.clearedAll 3 raw00055 (IntegerComputedClassCell.leftNumerator ![(19/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/3200),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00055_transform
theorem leaf00055_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00055=true := by decide +kernel
#print axioms leaf00055_sign
theorem leaf00055_log : RationalLog.accepts (3679550213/4294967296) (-20757233/268435456) 1 8=true := by decide +kernel
#print axioms leaf00055_log
def leaf00055 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (9211802153/200000000000) (3679550213/4294967296) (-20757233/268435456) 1 8 ![52,0,4] ![(19/3200),0,(1/4)] ![(1/3200),1,(1/4)] affine00055
theorem leaf00055_checked : FastNestedCellData.accepts 1 0 4 leaf00055=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (9211802153/200000000000) (3679550213/4294967296) (-20757233/268435456) 1 8 ![52,0,4] ![(19/3200),0,(1/4)] ![(1/3200),1,(1/4)] 57897021047372278798273740800000000000 51885651728803264988753308336611393536 1126503823400195533677422182400000000000 raw00055 affine00055
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00055_raw leaf00055_rectangular
    leaf00055_transform leaf00055_sign leaf00055_log
#print axioms leaf00055_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
