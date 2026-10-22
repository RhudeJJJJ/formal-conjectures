/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0827 : Family 10 := level10.get ⟨535,by decide⟩
def sourceMap0827 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0827 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0827_checked : acceptsGraphIso
    (source (graph core0827) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2023.graph sourceMap0827=true := by decide +kernel
theorem fusedMap0827_checked : acceptsGraphIso
    (fused (graph core0827) (root 10) 2 2) DegreeTwoThreeSpectrum5184.graph fusedMap0827=true := by decide +kernel
theorem certified0827 : Certified (graph core0827) (root 10) 2 2 :=
  of_native_maps core0827 DegreeOneMiddleResidualSpectrum2023.graph DegreeTwoThreeSpectrum5184.graph
    sourceMap0827 fusedMap0827 sourceMap0827_checked fusedMap0827_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0827
#print axioms sourceMap0827_checked
#print axioms fusedMap0827_checked
#print axioms certified0827
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
