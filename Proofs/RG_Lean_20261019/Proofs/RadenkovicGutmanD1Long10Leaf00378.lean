/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00378 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2233544654488668711772426862592000000000000 2462006578777112282654866037276909833814016 6777866917386201471400548499456000000000000))
theorem leaf00378_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2233544654488668711772426862592000000000000 2462006578777112282654866037276909833814016 6777866917386201471400548499456000000000000 raw00378=true := by decide +kernel
#print axioms leaf00378_raw
theorem leaf00378_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00378=true := by decide +kernel
#print axioms leaf00378_rectangular
def affine00378 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00378 (IntegerComputedClassCell.leftNumerator ![(31/80),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/80),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/80),0,0] ![(3/80),1,(1/4)]))
theorem leaf00378_transform : affine00378=(NestedInteger.clearedAll 3 raw00378 (IntegerComputedClassCell.leftNumerator ![(31/80),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/80),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/80),0,0] ![(3/80),1,(1/4)])) := by decide +kernel
#print axioms leaf00378_transform
theorem leaf00378_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00378=true := by decide +kernel
#print axioms leaf00378_sign
theorem leaf00378_log : RationalLog.accepts (3472813353/4294967296) (-456295023/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00378_log
def leaf00378 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (363242095011/1000000000000) (3472813353/4294967296) (-456295023/4294967296) 1 8 ![52,0,4] ![(31/80),0,0] ![(3/80),1,(1/4)] affine00378
theorem leaf00378_checked : FastNestedCellData.accepts 1 0 4 leaf00378=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (363242095011/1000000000000) (3472813353/4294967296) (-456295023/4294967296) 1 8 ![52,0,4] ![(31/80),0,0] ![(3/80),1,(1/4)] 2233544654488668711772426862592000000000000 2462006578777112282654866037276909833814016 6777866917386201471400548499456000000000000 raw00378 affine00378
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00378_raw leaf00378_rectangular
    leaf00378_transform leaf00378_sign leaf00378_log
#print axioms leaf00378_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
