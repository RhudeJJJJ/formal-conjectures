/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00147 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 370985367793457029695372106137600000000000 2548455299913661769744550675658070556672 6335924106711514553805438976000000000000))
theorem leaf00147_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 370985367793457029695372106137600000000000 2548455299913661769744550675658070556672 6335924106711514553805438976000000000000 raw00147=true := by decide +kernel
#print axioms leaf00147_raw
theorem leaf00147_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00147=true := by decide +kernel
#print axioms leaf00147_rectangular
def affine00147 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00147 (IntegerComputedClassCell.leftNumerator ![(31/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/1600),0,0] ![(1/1600),1,(1/4)]))
theorem leaf00147_transform : affine00147=(NestedInteger.clearedAll 3 raw00147 (IntegerComputedClassCell.leftNumerator ![(31/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/1600),0,0] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00147_transform
theorem leaf00147_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00147=true := by decide +kernel
#print axioms leaf00147_sign
theorem leaf00147_log : RationalLog.accepts (21040835/4294967296) (-5710947445/2147483648) 8 8=true := by decide +kernel
#print axioms leaf00147_log
def leaf00147 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (201111570861/500000000000) (21040835/4294967296) (-5710947445/2147483648) 8 8 ![52,0,4] ![(31/1600),0,0] ![(1/1600),1,(1/4)] affine00147
theorem leaf00147_checked : FastNestedCellData.accepts 1 0 4 leaf00147=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (201111570861/500000000000) (21040835/4294967296) (-5710947445/2147483648) 8 8 ![52,0,4] ![(31/1600),0,0] ![(1/1600),1,(1/4)] 370985367793457029695372106137600000000000 2548455299913661769744550675658070556672 6335924106711514553805438976000000000000 raw00147 affine00147
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00147_raw leaf00147_rectangular
    leaf00147_transform leaf00147_sign leaf00147_log
#print axioms leaf00147_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
