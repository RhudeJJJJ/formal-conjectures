/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00316 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4155962387172068710317767524352000000000000 2520840881726858299228957823303354136133632 11189058577453000702152048377856000000000000))
theorem leaf00316_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4155962387172068710317767524352000000000000 2520840881726858299228957823303354136133632 11189058577453000702152048377856000000000000 raw00316=true := by decide +kernel
#print axioms leaf00316_raw
theorem leaf00316_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00316=true := by decide +kernel
#print axioms leaf00316_rectangular
def affine00316 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00316 (IntegerComputedClassCell.leftNumerator ![(47/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(47/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(47/6400),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00316_transform : affine00316=(NestedInteger.clearedAll 3 raw00316 (IntegerComputedClassCell.leftNumerator ![(47/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(47/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(47/6400),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00316_transform
theorem leaf00316_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00316=true := by decide +kernel
#print axioms leaf00316_sign
theorem leaf00316_log : RationalLog.accepts (2126145413/4294967296) (-47186477/134217728) 2 8=true := by decide +kernel
#print axioms leaf00316_log
def leaf00316 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (225295172447/1000000000000) (2126145413/4294967296) (-47186477/134217728) 2 8 ![60,0,4] ![(47/6400),0,(1/16)] ![(1/6400),1,(1/16)] affine00316
theorem leaf00316_checked : FastNestedCellData.accepts 1 2 4 leaf00316=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (225295172447/1000000000000) (2126145413/4294967296) (-47186477/134217728) 2 8 ![60,0,4] ![(47/6400),0,(1/16)] ![(1/6400),1,(1/16)] 4155962387172068710317767524352000000000000 2520840881726858299228957823303354136133632 11189058577453000702152048377856000000000000 raw00316 affine00316
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00316_raw leaf00316_rectangular
    leaf00316_transform leaf00316_sign leaf00316_log
#print axioms leaf00316_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
