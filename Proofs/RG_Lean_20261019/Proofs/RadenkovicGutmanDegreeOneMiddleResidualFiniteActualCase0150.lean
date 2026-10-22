/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0150 : Family 8 := level8.get ⟨150,by decide⟩
def sourceMap0150 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0150 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0150_checked : acceptsGraphIso
    (source (graph core0150) (root 8) 2 2) DegreeOneMiddleResidualSpectrum316.graph sourceMap0150=true := by decide +kernel
theorem fusedMap0150_checked : acceptsGraphIso
    (fused (graph core0150) (root 8) 2 2) DegreeTwoThreeSpectrum2738.graph fusedMap0150=true := by decide +kernel
theorem certified0150 : Certified (graph core0150) (root 8) 2 2 :=
  of_native_maps core0150 DegreeOneMiddleResidualSpectrum316.graph DegreeTwoThreeSpectrum2738.graph
    sourceMap0150 fusedMap0150 sourceMap0150_checked fusedMap0150_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0150
#print axioms sourceMap0150_checked
#print axioms fusedMap0150_checked
#print axioms certified0150
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
