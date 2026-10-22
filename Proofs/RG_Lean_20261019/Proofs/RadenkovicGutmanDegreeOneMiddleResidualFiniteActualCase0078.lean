/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0078 : Family 8 := level8.get ⟨22,by decide⟩
def sourceMap0078 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap0078 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0078_checked : acceptsGraphIso
    (source (graph core0078) (root 8) 2 2) DegreeOneMiddleResidualSpectrum242.graph sourceMap0078=true := by decide +kernel
theorem fusedMap0078_checked : acceptsGraphIso
    (fused (graph core0078) (root 8) 2 2) DegreeTwoThreeSpectrum2398.graph fusedMap0078=true := by decide +kernel
theorem certified0078 : Certified (graph core0078) (root 8) 2 2 :=
  of_native_maps core0078 DegreeOneMiddleResidualSpectrum242.graph DegreeTwoThreeSpectrum2398.graph
    sourceMap0078 fusedMap0078 sourceMap0078_checked fusedMap0078_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0078
#print axioms sourceMap0078_checked
#print axioms fusedMap0078_checked
#print axioms certified0078
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
