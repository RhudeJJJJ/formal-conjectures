/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00573 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 492137393693641404382711067443200000000000 368197320791567360655089124151961893994496 2760221772335254902960497360896000000000000))
theorem leaf00573_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 492137393693641404382711067443200000000000 368197320791567360655089124151961893994496 2760221772335254902960497360896000000000000 raw00573=true := by decide +kernel
#print axioms leaf00573_raw
theorem leaf00573_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00573=true := by decide +kernel
#print axioms leaf00573_rectangular
def affine00573 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00573 (IntegerComputedClassCell.leftNumerator ![(57/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(57/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(57/3200),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00573_transform : affine00573=(NestedInteger.clearedAll 3 raw00573 (IntegerComputedClassCell.leftNumerator ![(57/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(57/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(57/3200),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00573_transform
theorem leaf00573_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00573=true := by decide +kernel
#print axioms leaf00573_sign
theorem leaf00573_log : RationalLog.accepts (2835131255/4294967296) (-111496203/536870912) 1 8=true := by decide +kernel
#print axioms leaf00573_log
def leaf00573 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (133394107851/1000000000000) (2835131255/4294967296) (-111496203/536870912) 1 8 ![60,0,4] ![(57/3200),0,(1/4)] ![(1/3200),1,(1/4)] affine00573
theorem leaf00573_checked : FastNestedCellData.accepts 1 2 4 leaf00573=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (133394107851/1000000000000) (2835131255/4294967296) (-111496203/536870912) 1 8 ![60,0,4] ![(57/3200),0,(1/4)] ![(1/3200),1,(1/4)] 492137393693641404382711067443200000000000 368197320791567360655089124151961893994496 2760221772335254902960497360896000000000000 raw00573 affine00573
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00573_raw leaf00573_rectangular
    leaf00573_transform leaf00573_sign leaf00573_log
#print axioms leaf00573_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
