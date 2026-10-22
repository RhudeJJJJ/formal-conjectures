/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00323 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 106008586347429270124595511296000000000 92948642705787039089418824268594020352 1617415987770035008835892019200000000000))
theorem leaf00323_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 106008586347429270124595511296000000000 92948642705787039089418824268594020352 1617415987770035008835892019200000000000 raw00323=true := by decide +kernel
#print axioms leaf00323_raw
theorem leaf00323_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00323=true := by decide +kernel
#print axioms leaf00323_rectangular
def affine00323 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00323 (IntegerComputedClassCell.leftNumerator ![(3/400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/400),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00323_transform : affine00323=(NestedInteger.clearedAll 3 raw00323 (IntegerComputedClassCell.leftNumerator ![(3/400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/400),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00323_transform
theorem leaf00323_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00323=true := by decide +kernel
#print axioms leaf00323_sign
theorem leaf00323_log : RationalLog.accepts (1780593975/2147483648) (-402330577/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00323_log
def leaf00323 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (5746736981/100000000000) (1780593975/2147483648) (-402330577/4294967296) 1 8 ![60,0,4] ![(3/400),0,(1/4)] ![(1/6400),1,(1/4)] affine00323
theorem leaf00323_checked : FastNestedCellData.accepts 1 2 4 leaf00323=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (5746736981/100000000000) (1780593975/2147483648) (-402330577/4294967296) 1 8 ![60,0,4] ![(3/400),0,(1/4)] ![(1/6400),1,(1/4)] 106008586347429270124595511296000000000 92948642705787039089418824268594020352 1617415987770035008835892019200000000000 raw00323 affine00323
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00323_raw leaf00323_rectangular
    leaf00323_transform leaf00323_sign leaf00323_log
#print axioms leaf00323_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
