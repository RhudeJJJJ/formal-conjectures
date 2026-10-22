/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00202 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 4346380009972727884626377310208000000000000 2688424163101356616401569022402836945698816 11410109650908938585448783020032000000000000))
theorem leaf00202_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 4346380009972727884626377310208000000000000 2688424163101356616401569022402836945698816 11410109650908938585448783020032000000000000 raw00202=true := by decide +kernel
#print axioms leaf00202_raw
theorem leaf00202_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00202=true := by decide +kernel
#print axioms leaf00202_rectangular
def affine00202 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00202 (IntegerComputedClassCell.leftNumerator ![(53/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(53/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(53/1600),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00202_transform : affine00202=(NestedInteger.clearedAll 3 raw00202 (IntegerComputedClassCell.leftNumerator ![(53/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(53/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(53/1600),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00202_transform
theorem leaf00202_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00202=true := by decide +kernel
#print axioms leaf00202_sign
theorem leaf00202_log : RationalLog.accepts (2150036459/4294967296) (-1485970977/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00202_log
def leaf00202 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (235617732463/1000000000000) (2150036459/4294967296) (-1485970977/4294967296) 1 8 ![52,0,4] ![(53/1600),0,(1/4)] ![(3/3200),1,(1/4)] affine00202
theorem leaf00202_checked : FastNestedCellData.accepts 1 0 4 leaf00202=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (235617732463/1000000000000) (2150036459/4294967296) (-1485970977/4294967296) 1 8 ![52,0,4] ![(53/1600),0,(1/4)] ![(3/3200),1,(1/4)] 4346380009972727884626377310208000000000000 2688424163101356616401569022402836945698816 11410109650908938585448783020032000000000000 raw00202 affine00202
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00202_raw leaf00202_rectangular
    leaf00202_transform leaf00202_sign leaf00202_log
#print axioms leaf00202_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
