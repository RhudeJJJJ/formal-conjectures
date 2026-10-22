/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00868 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 25463244072662544987512111104000000000000 13680251856913446941159701547613920690176 38713293240604871791250243584000000000000))
theorem leaf00868_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 25463244072662544987512111104000000000000 13680251856913446941159701547613920690176 38713293240604871791250243584000000000000 raw00868=true := by decide +kernel
#print axioms leaf00868_raw
theorem leaf00868_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00868=true := by decide +kernel
#print axioms leaf00868_rectangular
def affine00868 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00868 (IntegerComputedClassCell.leftNumerator ![(37/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/640),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00868_transform : affine00868=(NestedInteger.clearedAll 3 raw00868 (IntegerComputedClassCell.leftNumerator ![(37/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/640),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00868_transform
theorem leaf00868_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00868=true := by decide +kernel
#print axioms leaf00868_sign
theorem leaf00868_log : RationalLog.accepts (106562051/268435456) (-248002975/536870912) 2 8=true := by decide +kernel
#print axioms leaf00868_log
def leaf00868 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (353373498139/1000000000000) (106562051/268435456) (-248002975/536870912) 2 8 ![60,0,4] ![(37/640),0,(1/4)] ![(1/640),1,(1/4)] affine00868
theorem leaf00868_checked : FastNestedCellData.accepts 1 2 4 leaf00868=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (353373498139/1000000000000) (106562051/268435456) (-248002975/536870912) 2 8 ![60,0,4] ![(37/640),0,(1/4)] ![(1/640),1,(1/4)] 25463244072662544987512111104000000000000 13680251856913446941159701547613920690176 38713293240604871791250243584000000000000 raw00868 affine00868
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00868_raw leaf00868_rectangular
    leaf00868_transform leaf00868_sign leaf00868_log
#print axioms leaf00868_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
