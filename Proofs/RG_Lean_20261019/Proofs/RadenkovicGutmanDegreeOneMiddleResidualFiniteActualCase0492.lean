/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0492 : Family 10 := level10.get ⟨8,by decide⟩
def sourceMap0492 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![3,2,1,0,11,12,13,14,15,16,10,4,5,6,7,8,9] (sourceLabel 10 2 2 v)
def fusedMap0492 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (fusedLabel 10 2 2 v)
theorem sourceMap0492_checked : acceptsGraphIso
    (source (graph core0492) (root 10) 2 2) DegreeTwoThreeSpectrum5665.graph sourceMap0492=true := by decide +kernel
theorem fusedMap0492_checked : acceptsGraphIso
    (fused (graph core0492) (root 10) 2 2) DegreeTwoThreeSpectrum4965.graph fusedMap0492=true := by decide +kernel
theorem certified0492 : Certified (graph core0492) (root 10) 2 2 :=
  of_native_maps core0492 DegreeTwoThreeSpectrum5665.graph DegreeTwoThreeSpectrum4965.graph
    sourceMap0492 fusedMap0492 sourceMap0492_checked fusedMap0492_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0492
#print axioms sourceMap0492_checked
#print axioms fusedMap0492_checked
#print axioms certified0492
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
