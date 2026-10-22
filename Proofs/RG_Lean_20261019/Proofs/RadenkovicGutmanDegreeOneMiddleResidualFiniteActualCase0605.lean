/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0605 : Family 10 := level10.get ⟨156,by decide⟩
def sourceMap0605 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0605 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0605_checked : acceptsGraphIso
    (source (graph core0605) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1940.graph sourceMap0605=true := by decide +kernel
theorem fusedMap0605_checked : acceptsGraphIso
    (fused (graph core0605) (root 10) 2 2) DegreeTwoThreeSpectrum5093.graph fusedMap0605=true := by decide +kernel
theorem certified0605 : Certified (graph core0605) (root 10) 2 2 :=
  of_native_maps core0605 DegreeOneMiddleResidualSpectrum1940.graph DegreeTwoThreeSpectrum5093.graph
    sourceMap0605 fusedMap0605 sourceMap0605_checked fusedMap0605_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0605
#print axioms sourceMap0605_checked
#print axioms fusedMap0605_checked
#print axioms certified0605
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
