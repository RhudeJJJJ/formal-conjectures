/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0872 : Family 10 := level10.get ⟨617,by decide⟩
def sourceMap0872 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0872 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0872_checked : acceptsGraphIso
    (source (graph core0872) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2108.graph sourceMap0872=true := by decide +kernel
theorem fusedMap0872_checked : acceptsGraphIso
    (fused (graph core0872) (root 10) 2 2) DegreeTwoThreeSpectrum5307.graph fusedMap0872=true := by decide +kernel
theorem certified0872 : Certified (graph core0872) (root 10) 2 2 :=
  of_native_maps core0872 DegreeOneMiddleResidualSpectrum2108.graph DegreeTwoThreeSpectrum5307.graph
    sourceMap0872 fusedMap0872 sourceMap0872_checked fusedMap0872_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0872
#print axioms sourceMap0872_checked
#print axioms fusedMap0872_checked
#print axioms certified0872
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
