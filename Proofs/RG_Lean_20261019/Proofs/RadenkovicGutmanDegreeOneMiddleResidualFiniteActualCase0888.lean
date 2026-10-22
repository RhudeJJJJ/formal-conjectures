/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0888 : Family 10 := level10.get ⟨643,by decide⟩
def sourceMap0888 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0888 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0888_checked : acceptsGraphIso
    (source (graph core0888) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2131.graph sourceMap0888=true := by decide +kernel
theorem fusedMap0888_checked : acceptsGraphIso
    (fused (graph core0888) (root 10) 2 2) DegreeTwoThreeSpectrum5341.graph fusedMap0888=true := by decide +kernel
theorem certified0888 : Certified (graph core0888) (root 10) 2 2 :=
  of_native_maps core0888 DegreeOneMiddleResidualSpectrum2131.graph DegreeTwoThreeSpectrum5341.graph
    sourceMap0888 fusedMap0888 sourceMap0888_checked fusedMap0888_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0888
#print axioms sourceMap0888_checked
#print axioms fusedMap0888_checked
#print axioms certified0888
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
