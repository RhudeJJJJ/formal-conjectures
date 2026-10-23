/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerScaledCell
import Proofs.RadenkovicGutmanD1IntegerNorm00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMControls00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01753 : NestedInteger.Poly 3 := rg_integer_data% (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 168684840550400000000000 168685162242004389465867 107374387168685161977000000000000))
theorem leaf01753_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 168684840550400000000000 168685162242004389465867 107374387168685161977000000000000 raw01753=true := by decide +kernel
#print axioms leaf01753_raw
theorem leaf01753_rectangular : NestedInteger.rectangular 3 ![88,4,4] raw01753=true := by decide +kernel
#print axioms leaf01753_rectangular
def inner01753 : NestedInteger.Poly 3 := rg_integer_data% (IntegerAffineStages.inner raw01753 ![1,0,0] ![1,1,1] ![1024,1,1])
theorem leaf01753_inner : inner01753=(IntegerAffineStages.inner raw01753 ![1,0,0] ![1,1,1] ![1024,1,1]) := by decide +kernel
#print axioms leaf01753_inner
def affine01753 : NestedInteger.Poly 3 := rg_integer_data% (IntegerOuterTerms.transform 1 1 1024 0 inner01753)
theorem leaf01753_outer : affine01753=(IntegerOuterTerms.transform 1 1 1024 0 inner01753) := by decide +kernel
#print axioms leaf01753_outer
theorem leaf01753_sign : NestedInteger.bernsteinCheck 3 ![88,4,4] affine01753=true := by decide +kernel
#print axioms leaf01753_sign
theorem leaf01753_log : RationalLog.accepts (536871935/536870912) (4091/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01753_log
def leaf01753 : FastNestedCellData.Cell := IntegerScaledCell.make DegreeOneNormPack00.pack true (1571/1000000000000) (536871935/536870912) (4091/4294967296) 0 8 ![88,4,4] ![(1/1024),0,0] ![(1/1024),1,1] 168684840550400000000000 ![1024,1,1] affine01753
theorem leaf01753_checked : FastNestedCellData.accepts 1 4 4 leaf01753=true :=
  IntegerScaledCell.accepts_make DegreeOneIntegerNorm00.pack true (1571/1000000000000) (536871935/536870912) (4091/4294967296) 0 8 ![88,4,4] ![(1/1024),0,0] ![(1/1024),1,1] 168684840550400000000000 168685162242004389465867 107374387168685161977000000000000 ![1,0,0] ![1,1,1] ![1024,1,1] raw01753 inner01753 affine01753
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    leaf01753_raw leaf01753_rectangular leaf01753_inner leaf01753_outer leaf01753_sign leaf01753_log
#print axioms leaf01753_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLCMControls00
