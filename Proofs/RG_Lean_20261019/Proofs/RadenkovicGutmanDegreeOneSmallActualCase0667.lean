/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0667 : Family 7 := level7.get ⟨54,by decide⟩
def sourceMap0667 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 7 1 1 v)
def fusedMap0667 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0667_checked : acceptsGraphIso
    (source (graph core0667) (root 7) 1 1) SmallGeFourSpectrum177.graph sourceMap0667=true := by decide +kernel
theorem fusedMap0667_checked : acceptsGraphIso
    (fused (graph core0667) (root 7) 1 1) SmallGeFourSpectrum110.graph fusedMap0667=true := by decide +kernel
theorem certified0667 : Certified (graph core0667) (root 7) 1 1 :=
  of_native_maps core0667 SmallGeFourSpectrum177.graph SmallGeFourSpectrum110.graph
    sourceMap0667 fusedMap0667 sourceMap0667_checked fusedMap0667_checked
    DegreeOneSmallComparisons.comparison0667
#print axioms sourceMap0667_checked
#print axioms fusedMap0667_checked
#print axioms certified0667
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
