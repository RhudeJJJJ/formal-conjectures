/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00106 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 3856596507891394143269683200000000000 3174396583644330178003560859611168768 37069502194418772292822630400000000000))
theorem leaf00106_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 3856596507891394143269683200000000000 3174396583644330178003560859611168768 37069502194418772292822630400000000000 raw00106=true := by decide +kernel
#print axioms leaf00106_raw
theorem leaf00106_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00106=true := by decide +kernel
#print axioms leaf00106_rectangular
def affine00106 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00106 (IntegerComputedClassCell.leftNumerator ![(9/800),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/800),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/800),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00106_transform : affine00106=(NestedInteger.clearedAll 3 raw00106 (IntegerComputedClassCell.leftNumerator ![(9/800),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/800),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/800),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00106_transform
theorem leaf00106_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00106=true := by decide +kernel
#print axioms leaf00106_sign
theorem leaf00106_log : RationalLog.accepts (25440379/33554432) (-37155673/268435456) 1 8=true := by decide +kernel
#print axioms leaf00106_log
def leaf00106 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (17126728959/200000000000) (25440379/33554432) (-37155673/268435456) 1 8 ![52,0,4] ![(9/800),0,(1/4)] ![(1/3200),1,(1/4)] affine00106
theorem leaf00106_checked : FastNestedCellData.accepts 1 0 4 leaf00106=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (17126728959/200000000000) (25440379/33554432) (-37155673/268435456) 1 8 ![52,0,4] ![(9/800),0,(1/4)] ![(1/3200),1,(1/4)] 3856596507891394143269683200000000000 3174396583644330178003560859611168768 37069502194418772292822630400000000000 raw00106 affine00106
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00106_raw leaf00106_rectangular
    leaf00106_transform leaf00106_sign leaf00106_log
#print axioms leaf00106_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
