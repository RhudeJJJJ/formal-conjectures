/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0782 : Family 10 := level10.get ⟨442,by decide⟩
def sourceMap0782 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0782 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0782_checked : acceptsGraphIso
    (source (graph core0782) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1858.graph sourceMap0782=true := by decide +kernel
theorem fusedMap0782_checked : acceptsGraphIso
    (fused (graph core0782) (root 10) 2 2) DegreeTwoThreeSpectrum5860.graph fusedMap0782=true := by decide +kernel
theorem certified0782 : Certified (graph core0782) (root 10) 2 2 :=
  of_native_maps core0782 DegreeOneMiddleResidualSpectrum1858.graph DegreeTwoThreeSpectrum5860.graph
    sourceMap0782 fusedMap0782 sourceMap0782_checked fusedMap0782_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0782
#print axioms sourceMap0782_checked
#print axioms fusedMap0782_checked
#print axioms certified0782
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
