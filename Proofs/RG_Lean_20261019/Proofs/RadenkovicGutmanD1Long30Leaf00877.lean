/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00877 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 103735407091064193047678356029440000000000 39727846162909502383204641273767522205696 70646024469115284035777593344000000000000))
theorem leaf00877_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 103735407091064193047678356029440000000000 39727846162909502383204641273767522205696 70646024469115284035777593344000000000000 raw00877=true := by decide +kernel
#print axioms leaf00877_raw
theorem leaf00877_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00877=true := by decide +kernel
#print axioms leaf00877_rectangular
def affine00877 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00877 (IntegerComputedClassCell.leftNumerator ![(39/640),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(39/640),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(39/640),0,(1/8)] ![(1/640),1,(1/8)]))
theorem leaf00877_transform : affine00877=(NestedInteger.clearedAll 3 raw00877 (IntegerComputedClassCell.leftNumerator ![(39/640),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(39/640),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(39/640),0,(1/8)] ![(1/640),1,(1/8)])) := by decide +kernel
#print axioms leaf00877_transform
theorem leaf00877_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00877=true := by decide +kernel
#print axioms leaf00877_sign
theorem leaf00877_log : RationalLog.accepts (526404175/2147483648) (-1509662513/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00877_log
def leaf00877 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (562350768659/1000000000000) (526404175/2147483648) (-1509662513/2147483648) 3 8 ![60,0,4] ![(39/640),0,(1/8)] ![(1/640),1,(1/8)] affine00877
theorem leaf00877_checked : FastNestedCellData.accepts 1 2 4 leaf00877=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (562350768659/1000000000000) (526404175/2147483648) (-1509662513/2147483648) 3 8 ![60,0,4] ![(39/640),0,(1/8)] ![(1/640),1,(1/8)] 103735407091064193047678356029440000000000 39727846162909502383204641273767522205696 70646024469115284035777593344000000000000 raw00877 affine00877
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00877_raw leaf00877_rectangular
    leaf00877_transform leaf00877_sign leaf00877_log
#print axioms leaf00877_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
