/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00944 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 62309021174649236859344283238400000000000 41122764272271674147925576298096989569024 152181235925656625563012431872000000000000))
theorem leaf00944_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 62309021174649236859344283238400000000000 41122764272271674147925576298096989569024 152181235925656625563012431872000000000000 raw00944=true := by decide +kernel
#print axioms leaf00944_raw
theorem leaf00944_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00944=true := by decide +kernel
#print axioms leaf00944_rectangular
def affine00944 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00944 (IntegerComputedClassCell.leftNumerator ![(29/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(29/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(29/320),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00944_transform : affine00944=(NestedInteger.clearedAll 3 raw00944 (IntegerComputedClassCell.leftNumerator ![(29/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(29/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(29/320),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00944_transform
theorem leaf00944_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00944=true := by decide +kernel
#print axioms leaf00944_sign
theorem leaf00944_log : RationalLog.accepts (2231575055/4294967296) (-703017769/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00944_log
def leaf00944 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (67555576123/250000000000) (2231575055/4294967296) (-703017769/2147483648) 1 8 ![60,0,4] ![(29/320),0,(1/2)] ![(1/320),1,(1/2)] affine00944
theorem leaf00944_checked : FastNestedCellData.accepts 1 2 4 leaf00944=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (67555576123/250000000000) (2231575055/4294967296) (-703017769/2147483648) 1 8 ![60,0,4] ![(29/320),0,(1/2)] ![(1/320),1,(1/2)] 62309021174649236859344283238400000000000 41122764272271674147925576298096989569024 152181235925656625563012431872000000000000 raw00944 affine00944
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00944_raw leaf00944_rectangular
    leaf00944_transform leaf00944_sign leaf00944_log
#print axioms leaf00944_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
