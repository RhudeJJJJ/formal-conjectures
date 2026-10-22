/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0059 : Family 8 := level8.get ⟨0,by decide⟩
def sourceMap0059 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,3,4,5,6,7,8] (sourceLabel 8 2 2 v)
def fusedMap0059 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,2,3,4,5,6,7] (fusedLabel 8 2 2 v)
theorem sourceMap0059_checked : acceptsGraphIso
    (source (graph core0059) (root 8) 2 2) DegreeTwoThreeSpectrum2381.graph sourceMap0059=true := by decide +kernel
theorem fusedMap0059_checked : acceptsGraphIso
    (fused (graph core0059) (root 8) 2 2) DegreeOneMiddleResidualSpectrum111.graph fusedMap0059=true := by decide +kernel
theorem certified0059 : Certified (graph core0059) (root 8) 2 2 :=
  of_native_maps core0059 DegreeTwoThreeSpectrum2381.graph DegreeOneMiddleResidualSpectrum111.graph
    sourceMap0059 fusedMap0059 sourceMap0059_checked fusedMap0059_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0059
#print axioms sourceMap0059_checked
#print axioms fusedMap0059_checked
#print axioms certified0059
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
