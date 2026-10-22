/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0600 : Family 10 := level10.get ⟨149,by decide⟩
def sourceMap0600 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0600 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0600_checked : acceptsGraphIso
    (source (graph core0600) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1889.graph sourceMap0600=true := by decide +kernel
theorem fusedMap0600_checked : acceptsGraphIso
    (fused (graph core0600) (root 10) 2 2) DegreeTwoThreeSpectrum5085.graph fusedMap0600=true := by decide +kernel
theorem certified0600 : Certified (graph core0600) (root 10) 2 2 :=
  of_native_maps core0600 DegreeOneMiddleResidualSpectrum1889.graph DegreeTwoThreeSpectrum5085.graph
    sourceMap0600 fusedMap0600 sourceMap0600_checked fusedMap0600_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0600
#print axioms sourceMap0600_checked
#print axioms fusedMap0600_checked
#print axioms certified0600
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
