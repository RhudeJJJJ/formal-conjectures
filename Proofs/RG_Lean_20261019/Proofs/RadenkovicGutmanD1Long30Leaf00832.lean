/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00832 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 475749151075323318645453697843200000000000 184511548892396189452397023425334043738112 357713441355452499766676553728000000000000))
theorem leaf00832_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 475749151075323318645453697843200000000000 184511548892396189452397023425334043738112 357713441355452499766676553728000000000000 raw00832=true := by decide +kernel
#print axioms leaf00832_raw
theorem leaf00832_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00832=true := by decide +kernel
#print axioms leaf00832_rectangular
def affine00832 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00832 (IntegerComputedClassCell.leftNumerator ![(77/1600),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(77/1600),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(77/1600),0,(1/8)] ![(3/3200),1,(1/8)]))
theorem leaf00832_transform : affine00832=(NestedInteger.clearedAll 3 raw00832 (IntegerComputedClassCell.leftNumerator ![(77/1600),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(77/1600),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(77/1600),0,(1/8)] ![(3/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00832_transform
theorem leaf00832_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00832=true := by decide +kernel
#print axioms leaf00832_sign
theorem leaf00832_log : RationalLog.accepts (1098907465/4294967296) (-2927294019/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00832_log
def leaf00832 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (257904131577/500000000000) (1098907465/4294967296) (-2927294019/4294967296) 2 8 ![60,0,4] ![(77/1600),0,(1/8)] ![(3/3200),1,(1/8)] affine00832
theorem leaf00832_checked : FastNestedCellData.accepts 1 2 4 leaf00832=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (257904131577/500000000000) (1098907465/4294967296) (-2927294019/4294967296) 2 8 ![60,0,4] ![(77/1600),0,(1/8)] ![(3/3200),1,(1/8)] 475749151075323318645453697843200000000000 184511548892396189452397023425334043738112 357713441355452499766676553728000000000000 raw00832 affine00832
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00832_raw leaf00832_rectangular
    leaf00832_transform leaf00832_sign leaf00832_log
#print axioms leaf00832_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
