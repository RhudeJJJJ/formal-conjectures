/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00847 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3270489338359453982769169825792000000000000 1254039379945957968479187070692377959071744 2357745391888916366344327266304000000000000))
theorem leaf00847_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3270489338359453982769169825792000000000000 1254039379945957968479187070692377959071744 2357745391888916366344327266304000000000000 raw00847=true := by decide +kernel
#print axioms leaf00847_raw
theorem leaf00847_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00847=true := by decide +kernel
#print axioms leaf00847_rectangular
def affine00847 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00847 (IntegerComputedClassCell.leftNumerator ![(33/640),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(33/640),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(33/640),0,(1/8)] ![(1/640),1,(1/8)]))
theorem leaf00847_transform : affine00847=(NestedInteger.clearedAll 3 raw00847 (IntegerComputedClassCell.leftNumerator ![(33/640),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(33/640),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(33/640),0,(1/8)] ![(1/640),1,(1/8)])) := by decide +kernel
#print axioms leaf00847_transform
theorem leaf00847_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00847=true := by decide +kernel
#print axioms leaf00847_sign
theorem leaf00847_log : RationalLog.accepts (1075061577/4294967296) (-1487203329/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00847_log
def leaf00847 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (531880746861/1000000000000) (1075061577/4294967296) (-1487203329/2147483648) 2 8 ![60,0,4] ![(33/640),0,(1/8)] ![(1/640),1,(1/8)] affine00847
theorem leaf00847_checked : FastNestedCellData.accepts 1 2 4 leaf00847=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (531880746861/1000000000000) (1075061577/4294967296) (-1487203329/2147483648) 2 8 ![60,0,4] ![(33/640),0,(1/8)] ![(1/640),1,(1/8)] 3270489338359453982769169825792000000000000 1254039379945957968479187070692377959071744 2357745391888916366344327266304000000000000 raw00847 affine00847
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00847_raw leaf00847_rectangular
    leaf00847_transform leaf00847_sign leaf00847_log
#print axioms leaf00847_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
