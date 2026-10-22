/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00385 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 3448444264600463297272296243200000000000 4106614104813500647566048488236334972928 13729680253683416498564392550400000000000))
theorem leaf00385_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 3448444264600463297272296243200000000000 4106614104813500647566048488236334972928 13729680253683416498564392550400000000000 raw00385=true := by decide +kernel
#print axioms leaf00385_raw
theorem leaf00385_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00385=true := by decide +kernel
#print axioms leaf00385_rectangular
def affine00385 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00385 (IntegerComputedClassCell.leftNumerator ![(37/80),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/80),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/80),0,(1/4)] ![(3/80),1,(1/4)]))
theorem leaf00385_transform : affine00385=(NestedInteger.clearedAll 3 raw00385 (IntegerComputedClassCell.leftNumerator ![(37/80),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/80),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/80),0,(1/4)] ![(3/80),1,(1/4)])) := by decide +kernel
#print axioms leaf00385_transform
theorem leaf00385_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00385=true := by decide +kernel
#print axioms leaf00385_sign
theorem leaf00385_log : RationalLog.accepts (984274753/1073741824) (-186830641/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00385_log
def leaf00385 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (29910486107/100000000000) (984274753/1073741824) (-186830641/4294967296) 1 8 ![52,0,4] ![(37/80),0,(1/4)] ![(3/80),1,(1/4)] affine00385
theorem leaf00385_checked : FastNestedCellData.accepts 1 0 4 leaf00385=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (29910486107/100000000000) (984274753/1073741824) (-186830641/4294967296) 1 8 ![52,0,4] ![(37/80),0,(1/4)] ![(3/80),1,(1/4)] 3448444264600463297272296243200000000000 4106614104813500647566048488236334972928 13729680253683416498564392550400000000000 raw00385 affine00385
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00385_raw leaf00385_rectangular
    leaf00385_transform leaf00385_sign leaf00385_log
#print axioms leaf00385_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
