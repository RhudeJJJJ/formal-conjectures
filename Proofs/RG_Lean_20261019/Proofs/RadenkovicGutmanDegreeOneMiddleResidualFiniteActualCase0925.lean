/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0925 : Family 10 := level10.get ⟨729,by decide⟩
def sourceMap0925 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0925 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0925_checked : acceptsGraphIso
    (source (graph core0925) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2195.graph sourceMap0925=true := by decide +kernel
theorem fusedMap0925_checked : acceptsGraphIso
    (fused (graph core0925) (root 10) 2 2) DegreeTwoThreeSpectrum5485.graph fusedMap0925=true := by decide +kernel
theorem certified0925 : Certified (graph core0925) (root 10) 2 2 :=
  of_native_maps core0925 DegreeOneMiddleResidualSpectrum2195.graph DegreeTwoThreeSpectrum5485.graph
    sourceMap0925 fusedMap0925 sourceMap0925_checked fusedMap0925_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0925
#print axioms sourceMap0925_checked
#print axioms fusedMap0925_checked
#print axioms certified0925
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
