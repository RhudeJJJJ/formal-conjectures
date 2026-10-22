/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0614 : Family 10 := level10.get ⟨170,by decide⟩
def sourceMap0614 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0614 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0614_checked : acceptsGraphIso
    (source (graph core0614) (root 10) 2 2) DegreeTwoThreeSpectrum6863.graph sourceMap0614=true := by decide +kernel
theorem fusedMap0614_checked : acceptsGraphIso
    (fused (graph core0614) (root 10) 2 2) DegreeTwoThreeSpectrum5112.graph fusedMap0614=true := by decide +kernel
theorem certified0614 : Certified (graph core0614) (root 10) 2 2 :=
  of_native_maps core0614 DegreeTwoThreeSpectrum6863.graph DegreeTwoThreeSpectrum5112.graph
    sourceMap0614 fusedMap0614 sourceMap0614_checked fusedMap0614_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0614
#print axioms sourceMap0614_checked
#print axioms fusedMap0614_checked
#print axioms certified0614
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
