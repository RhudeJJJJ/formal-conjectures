/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00548 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 141017348889138226004538425344000000000000 107823170799841384675757377788355022946304 881534458627233527457504034816000000000000))
theorem leaf00548_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 141017348889138226004538425344000000000000 107823170799841384675757377788355022946304 881534458627233527457504034816000000000000 raw00548=true := by decide +kernel
#print axioms leaf00548_raw
theorem leaf00548_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00548=true := by decide +kernel
#print axioms leaf00548_rectangular
def affine00548 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00548 (IntegerComputedClassCell.leftNumerator ![(13/800),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/800),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/800),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00548_transform : affine00548=(NestedInteger.clearedAll 3 raw00548 (IntegerComputedClassCell.leftNumerator ![(13/800),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/800),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/800),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00548_transform
theorem leaf00548_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00548=true := by decide +kernel
#print axioms leaf00548_sign
theorem leaf00548_log : RationalLog.accepts (731518661/1073741824) (-103020735/536870912) 1 8=true := by decide +kernel
#print axioms leaf00548_log
def leaf00548 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (122313052819/1000000000000) (731518661/1073741824) (-103020735/536870912) 1 8 ![60,0,4] ![(13/800),0,(1/4)] ![(1/3200),1,(1/4)] affine00548
theorem leaf00548_checked : FastNestedCellData.accepts 1 2 4 leaf00548=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (122313052819/1000000000000) (731518661/1073741824) (-103020735/536870912) 1 8 ![60,0,4] ![(13/800),0,(1/4)] ![(1/3200),1,(1/4)] 141017348889138226004538425344000000000000 107823170799841384675757377788355022946304 881534458627233527457504034816000000000000 raw00548 affine00548
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00548_raw leaf00548_rectangular
    leaf00548_transform leaf00548_sign leaf00548_log
#print axioms leaf00548_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
