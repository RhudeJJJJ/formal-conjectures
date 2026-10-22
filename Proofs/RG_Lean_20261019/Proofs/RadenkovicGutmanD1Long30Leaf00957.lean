/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00957 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 33716656540597748982035251200000000000 15096841339294324663356373217549746176 25206432074697067070488576000000000000))
theorem leaf00957_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 33716656540597748982035251200000000000 15096841339294324663356373217549746176 25206432074697067070488576000000000000 raw00957=true := by decide +kernel
#print axioms leaf00957_raw
theorem leaf00957_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00957=true := by decide +kernel
#print axioms leaf00957_rectangular
def affine00957 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00957 (IntegerComputedClassCell.leftNumerator ![(1/10),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/10),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/10),0,(1/8)] ![(1/320),1,(1/8)]))
theorem leaf00957_transform : affine00957=(NestedInteger.clearedAll 3 raw00957 (IntegerComputedClassCell.leftNumerator ![(1/10),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/10),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/10),0,(1/8)] ![(1/320),1,(1/8)])) := by decide +kernel
#print axioms leaf00957_transform
theorem leaf00957_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00957=true := by decide +kernel
#print axioms leaf00957_sign
theorem leaf00957_log : RationalLog.accepts (18792845/67108864) (-2733402995/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00957_log
def leaf00957 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (149732033619/250000000000) (18792845/67108864) (-2733402995/4294967296) 2 8 ![60,0,4] ![(1/10),0,(1/8)] ![(1/320),1,(1/8)] affine00957
theorem leaf00957_checked : FastNestedCellData.accepts 1 2 4 leaf00957=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (149732033619/250000000000) (18792845/67108864) (-2733402995/4294967296) 2 8 ![60,0,4] ![(1/10),0,(1/8)] ![(1/320),1,(1/8)] 33716656540597748982035251200000000000 15096841339294324663356373217549746176 25206432074697067070488576000000000000 raw00957 affine00957
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00957_raw leaf00957_rectangular
    leaf00957_transform leaf00957_sign leaf00957_log
#print axioms leaf00957_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
