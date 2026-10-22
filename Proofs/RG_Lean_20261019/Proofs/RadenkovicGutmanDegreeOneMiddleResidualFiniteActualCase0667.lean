/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0667 : Family 10 := level10.get ⟨251,by decide⟩
def sourceMap0667 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0667 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0667_checked : acceptsGraphIso
    (source (graph core0667) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1679.graph sourceMap0667=true := by decide +kernel
theorem fusedMap0667_checked : acceptsGraphIso
    (fused (graph core0667) (root 10) 2 2) DegreeTwoThreeSpectrum5345.graph fusedMap0667=true := by decide +kernel
theorem certified0667 : Certified (graph core0667) (root 10) 2 2 :=
  of_native_maps core0667 DegreeOneMiddleResidualSpectrum1679.graph DegreeTwoThreeSpectrum5345.graph
    sourceMap0667 fusedMap0667 sourceMap0667_checked fusedMap0667_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0667
#print axioms sourceMap0667_checked
#print axioms fusedMap0667_checked
#print axioms certified0667
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
