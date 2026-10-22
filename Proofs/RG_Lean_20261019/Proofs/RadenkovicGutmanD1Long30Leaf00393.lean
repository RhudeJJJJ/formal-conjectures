/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00393 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 272376238515559926845843020185600000000000 230579882851206208164095014990642805735424 3123215233959658185840476028928000000000000))
theorem leaf00393_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 272376238515559926845843020185600000000000 230579882851206208164095014990642805735424 3123215233959658185840476028928000000000000 raw00393=true := by decide +kernel
#print axioms leaf00393_raw
theorem leaf00393_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00393=true := by decide +kernel
#print axioms leaf00393_rectangular
def affine00393 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00393 (IntegerComputedClassCell.leftNumerator ![(31/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/3200),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00393_transform : affine00393=(NestedInteger.clearedAll 3 raw00393 (IntegerComputedClassCell.leftNumerator ![(31/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/3200),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00393_transform
theorem leaf00393_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00393=true := by decide +kernel
#print axioms leaf00393_sign
theorem leaf00393_log : RationalLog.accepts (3385925855/4294967296) (-510707199/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00393_log
def leaf00393 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (73827727383/1000000000000) (3385925855/4294967296) (-510707199/4294967296) 1 8 ![60,0,4] ![(31/3200),0,(1/4)] ![(1/6400),1,(1/4)] affine00393
theorem leaf00393_checked : FastNestedCellData.accepts 1 2 4 leaf00393=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (73827727383/1000000000000) (3385925855/4294967296) (-510707199/4294967296) 1 8 ![60,0,4] ![(31/3200),0,(1/4)] ![(1/6400),1,(1/4)] 272376238515559926845843020185600000000000 230579882851206208164095014990642805735424 3123215233959658185840476028928000000000000 raw00393 affine00393
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00393_raw leaf00393_rectangular
    leaf00393_transform leaf00393_sign leaf00393_log
#print axioms leaf00393_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
