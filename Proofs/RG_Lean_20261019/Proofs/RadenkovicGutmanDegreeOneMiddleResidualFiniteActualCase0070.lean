/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0070 : Family 8 := level8.get ⟨12,by decide⟩
def sourceMap0070 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap0070 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0070_checked : acceptsGraphIso
    (source (graph core0070) (root 8) 2 2) DegreeOneMiddleResidualSpectrum205.graph sourceMap0070=true := by decide +kernel
theorem fusedMap0070_checked : acceptsGraphIso
    (fused (graph core0070) (root 8) 2 2) DegreeTwoThreeSpectrum2342.graph fusedMap0070=true := by decide +kernel
theorem certified0070 : Certified (graph core0070) (root 8) 2 2 :=
  of_native_maps core0070 DegreeOneMiddleResidualSpectrum205.graph DegreeTwoThreeSpectrum2342.graph
    sourceMap0070 fusedMap0070 sourceMap0070_checked fusedMap0070_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0070
#print axioms sourceMap0070_checked
#print axioms fusedMap0070_checked
#print axioms certified0070
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
