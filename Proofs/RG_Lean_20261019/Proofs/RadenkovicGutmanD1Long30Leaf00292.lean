/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00292 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 23598617929205519391749518131200000000000 18722481030169583317026197377466287259648 182939111638076969812867678208000000000000))
theorem leaf00292_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 23598617929205519391749518131200000000000 18722481030169583317026197377466287259648 182939111638076969812867678208000000000000 raw00292=true := by decide +kernel
#print axioms leaf00292_raw
theorem leaf00292_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00292=true := by decide +kernel
#print axioms leaf00292_rectangular
def affine00292 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00292 (IntegerComputedClassCell.leftNumerator ![(21/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(21/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(21/3200),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00292_transform : affine00292=(NestedInteger.clearedAll 3 raw00292 (IntegerComputedClassCell.leftNumerator ![(21/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(21/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(21/3200),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00292_transform
theorem leaf00292_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00292=true := by decide +kernel
#print axioms leaf00292_sign
theorem leaf00292_log : RationalLog.accepts (1545574945/2147483648) (-706309097/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00292_log
def leaf00292 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (51171345653/500000000000) (1545574945/2147483648) (-706309097/4294967296) 1 8 ![60,0,4] ![(21/3200),0,(1/8)] ![(1/6400),1,(1/8)] affine00292
theorem leaf00292_checked : FastNestedCellData.accepts 1 2 4 leaf00292=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (51171345653/500000000000) (1545574945/2147483648) (-706309097/4294967296) 1 8 ![60,0,4] ![(21/3200),0,(1/8)] ![(1/6400),1,(1/8)] 23598617929205519391749518131200000000000 18722481030169583317026197377466287259648 182939111638076969812867678208000000000000 raw00292 affine00292
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00292_raw leaf00292_rectangular
    leaf00292_transform leaf00292_sign leaf00292_log
#print axioms leaf00292_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
