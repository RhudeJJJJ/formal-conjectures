/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0644 : Family 10 := level10.get ⟨219,by decide⟩
def sourceMap0644 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0644 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0644_checked : acceptsGraphIso
    (source (graph core0644) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1618.graph sourceMap0644=true := by decide +kernel
theorem fusedMap0644_checked : acceptsGraphIso
    (fused (graph core0644) (root 10) 2 2) DegreeTwoThreeSpectrum5244.graph fusedMap0644=true := by decide +kernel
theorem certified0644 : Certified (graph core0644) (root 10) 2 2 :=
  of_native_maps core0644 DegreeOneMiddleResidualSpectrum1618.graph DegreeTwoThreeSpectrum5244.graph
    sourceMap0644 fusedMap0644 sourceMap0644_checked fusedMap0644_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0644
#print axioms sourceMap0644_checked
#print axioms fusedMap0644_checked
#print axioms certified0644
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
