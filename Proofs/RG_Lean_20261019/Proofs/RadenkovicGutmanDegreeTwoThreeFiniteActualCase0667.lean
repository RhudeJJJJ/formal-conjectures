/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0667 : Family 10 := level10.get ⟨880,by decide⟩
def sourceMap0667 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0667 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0667_checked : acceptsGraphIso
    (source (graph core0667) (root 10) 0 0) DegreeOneSmallSpectrum1669.graph sourceMap0667=true := by decide +kernel
theorem fusedMap0667_checked : acceptsGraphIso
    (fused (graph core0667) (root 10) 0 0) DegreeOneSmallSpectrum1431.graph fusedMap0667=true := by decide +kernel
theorem certified0667 : Certified (graph core0667) (root 10) 0 0 :=
  of_native_maps core0667 DegreeOneSmallSpectrum1669.graph DegreeOneSmallSpectrum1431.graph
    sourceMap0667 fusedMap0667 sourceMap0667_checked fusedMap0667_checked
    DegreeTwoThreeFiniteComparisons.comparison0667
#print axioms sourceMap0667_checked
#print axioms fusedMap0667_checked
#print axioms certified0667
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
