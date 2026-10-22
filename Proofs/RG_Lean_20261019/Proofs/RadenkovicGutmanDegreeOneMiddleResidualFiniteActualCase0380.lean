/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0380 : Family 9 := level9.get ⟨290,by decide⟩
def sourceMap0380 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0380 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0380_checked : acceptsGraphIso
    (source (graph core0380) (root 9) 2 2) DegreeOneMiddleResidualSpectrum900.graph sourceMap0380=true := by decide +kernel
theorem fusedMap0380_checked : acceptsGraphIso
    (fused (graph core0380) (root 9) 2 2) DegreeTwoThreeSpectrum4118.graph fusedMap0380=true := by decide +kernel
theorem certified0380 : Certified (graph core0380) (root 9) 2 2 :=
  of_native_maps core0380 DegreeOneMiddleResidualSpectrum900.graph DegreeTwoThreeSpectrum4118.graph
    sourceMap0380 fusedMap0380 sourceMap0380_checked fusedMap0380_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0380
#print axioms sourceMap0380_checked
#print axioms fusedMap0380_checked
#print axioms certified0380
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
