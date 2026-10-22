/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0726 : Family 10 := level10.get ⟨345,by decide⟩
def sourceMap0726 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0726 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0726_checked : acceptsGraphIso
    (source (graph core0726) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1814.graph sourceMap0726=true := by decide +kernel
theorem fusedMap0726_checked : acceptsGraphIso
    (fused (graph core0726) (root 10) 2 2) DegreeTwoThreeSpectrum5610.graph fusedMap0726=true := by decide +kernel
theorem certified0726 : Certified (graph core0726) (root 10) 2 2 :=
  of_native_maps core0726 DegreeOneMiddleResidualSpectrum1814.graph DegreeTwoThreeSpectrum5610.graph
    sourceMap0726 fusedMap0726 sourceMap0726_checked fusedMap0726_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0726
#print axioms sourceMap0726_checked
#print axioms fusedMap0726_checked
#print axioms certified0726
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
