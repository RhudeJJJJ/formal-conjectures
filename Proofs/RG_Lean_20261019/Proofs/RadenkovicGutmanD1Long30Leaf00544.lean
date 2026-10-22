/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00544 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 271800571192767927345706172416000000000000 237983889195119163039136939340885806546944 4037912685745327938940421799936000000000000))
theorem leaf00544_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 271800571192767927345706172416000000000000 237983889195119163039136939340885806546944 4037912685745327938940421799936000000000000 raw00544=true := by decide +kernel
#print axioms leaf00544_raw
theorem leaf00544_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00544=true := by decide +kernel
#print axioms leaf00544_rectangular
def affine00544 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00544 (IntegerComputedClassCell.leftNumerator ![(51/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(51/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(51/3200),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00544_transform : affine00544=(NestedInteger.clearedAll 3 raw00544 (IntegerComputedClassCell.leftNumerator ![(51/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(51/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(51/3200),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00544_transform
theorem leaf00544_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00544=true := by decide +kernel
#print axioms leaf00544_sign
theorem leaf00544_log : RationalLog.accepts (3551295291/4294967296) (-408304395/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00544_log
def leaf00544 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (29468676977/500000000000) (3551295291/4294967296) (-408304395/4294967296) 1 8 ![60,0,4] ![(51/3200),0,(1/2)] ![(1/3200),1,(1/2)] affine00544
theorem leaf00544_checked : FastNestedCellData.accepts 1 2 4 leaf00544=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (29468676977/500000000000) (3551295291/4294967296) (-408304395/4294967296) 1 8 ![60,0,4] ![(51/3200),0,(1/2)] ![(1/3200),1,(1/2)] 271800571192767927345706172416000000000000 237983889195119163039136939340885806546944 4037912685745327938940421799936000000000000 raw00544 affine00544
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00544_raw leaf00544_rectangular
    leaf00544_transform leaf00544_sign leaf00544_log
#print axioms leaf00544_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
