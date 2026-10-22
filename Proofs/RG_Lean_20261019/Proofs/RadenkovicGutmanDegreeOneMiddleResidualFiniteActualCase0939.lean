/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0939 : Family 10 := level10.get ⟨752,by decide⟩
def sourceMap0939 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0939 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0939_checked : acceptsGraphIso
    (source (graph core0939) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2217.graph sourceMap0939=true := by decide +kernel
theorem fusedMap0939_checked : acceptsGraphIso
    (fused (graph core0939) (root 10) 2 2) DegreeTwoThreeSpectrum5518.graph fusedMap0939=true := by decide +kernel
theorem certified0939 : Certified (graph core0939) (root 10) 2 2 :=
  of_native_maps core0939 DegreeOneMiddleResidualSpectrum2217.graph DegreeTwoThreeSpectrum5518.graph
    sourceMap0939 fusedMap0939 sourceMap0939_checked fusedMap0939_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0939
#print axioms sourceMap0939_checked
#print axioms fusedMap0939_checked
#print axioms certified0939
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
