/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00307 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 201821032048269124906904453120000000000 157728193291255105494368490938267860992 1441659268770609824883340738560000000000))
theorem leaf00307_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 201821032048269124906904453120000000000 157728193291255105494368490938267860992 1441659268770609824883340738560000000000 raw00307=true := by decide +kernel
#print axioms leaf00307_raw
theorem leaf00307_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00307=true := by decide +kernel
#print axioms leaf00307_rectangular
def affine00307 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00307 (IntegerComputedClassCell.leftNumerator ![(9/1280),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(9/1280),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(9/1280),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00307_transform : affine00307=(NestedInteger.clearedAll 3 raw00307 (IntegerComputedClassCell.leftNumerator ![(9/1280),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(9/1280),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(9/1280),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00307_transform
theorem leaf00307_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00307=true := by decide +kernel
#print axioms leaf00307_sign
theorem leaf00307_log : RationalLog.accepts (3025601373/4294967296) (-752336719/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00307_log
def leaf00307 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1094074007/10000000000) (3025601373/4294967296) (-752336719/4294967296) 1 8 ![60,0,4] ![(9/1280),0,(1/8)] ![(1/6400),1,(1/8)] affine00307
theorem leaf00307_checked : FastNestedCellData.accepts 1 2 4 leaf00307=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1094074007/10000000000) (3025601373/4294967296) (-752336719/4294967296) 1 8 ![60,0,4] ![(9/1280),0,(1/8)] ![(1/6400),1,(1/8)] 201821032048269124906904453120000000000 157728193291255105494368490938267860992 1441659268770609824883340738560000000000 raw00307 affine00307
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00307_raw leaf00307_rectangular
    leaf00307_transform leaf00307_sign leaf00307_log
#print axioms leaf00307_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
