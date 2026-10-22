/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00319 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5046261532438636039588932485120000000000 4734516854122011946832475218547673399296 173071530595932800157669654528000000000000))
theorem leaf00319_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5046261532438636039588932485120000000000 4734516854122011946832475218547673399296 173071530595932800157669654528000000000000 raw00319=true := by decide +kernel
#print axioms leaf00319_raw
theorem leaf00319_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00319=true := by decide +kernel
#print axioms leaf00319_rectangular
def affine00319 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00319 (IntegerComputedClassCell.leftNumerator ![(47/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(47/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(47/6400),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00319_transform : affine00319=(NestedInteger.clearedAll 3 raw00319 (IntegerComputedClassCell.leftNumerator ![(47/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(47/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(47/6400),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00319_transform
theorem leaf00319_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00319=true := by decide +kernel
#print axioms leaf00319_sign
theorem leaf00319_log : RationalLog.accepts (3922336775/4294967296) (-194897811/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00319_log
def leaf00319 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (13677919291/500000000000) (3922336775/4294967296) (-194897811/4294967296) 1 8 ![60,0,4] ![(47/6400),0,(1/2)] ![(1/6400),1,(1/2)] affine00319
theorem leaf00319_checked : FastNestedCellData.accepts 1 2 4 leaf00319=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (13677919291/500000000000) (3922336775/4294967296) (-194897811/4294967296) 1 8 ![60,0,4] ![(47/6400),0,(1/2)] ![(1/6400),1,(1/2)] 5046261532438636039588932485120000000000 4734516854122011946832475218547673399296 173071530595932800157669654528000000000000 raw00319 affine00319
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00319_raw leaf00319_rectangular
    leaf00319_transform leaf00319_sign leaf00319_log
#print axioms leaf00319_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
