/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0118 : Family 8 := level8.get ⟨84,by decide⟩
def sourceMap0118 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap0118 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0118_checked : acceptsGraphIso
    (source (graph core0118) (root 8) 2 2) DegreeTwoThreeSpectrum3634.graph sourceMap0118=true := by decide +kernel
theorem fusedMap0118_checked : acceptsGraphIso
    (fused (graph core0118) (root 8) 2 2) DegreeTwoThreeSpectrum2409.graph fusedMap0118=true := by decide +kernel
theorem certified0118 : Certified (graph core0118) (root 8) 2 2 :=
  of_native_maps core0118 DegreeTwoThreeSpectrum3634.graph DegreeTwoThreeSpectrum2409.graph
    sourceMap0118 fusedMap0118 sourceMap0118_checked fusedMap0118_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0118
#print axioms sourceMap0118_checked
#print axioms fusedMap0118_checked
#print axioms certified0118
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
