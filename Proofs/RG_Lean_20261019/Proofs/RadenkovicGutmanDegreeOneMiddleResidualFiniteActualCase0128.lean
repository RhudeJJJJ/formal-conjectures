/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0128 : Family 8 := level8.get ⟨104,by decide⟩
def sourceMap0128 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0128 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0128_checked : acceptsGraphIso
    (source (graph core0128) (root 8) 2 2) DegreeOneMiddleResidualSpectrum273.graph sourceMap0128=true := by decide +kernel
theorem fusedMap0128_checked : acceptsGraphIso
    (fused (graph core0128) (root 8) 2 2) DegreeTwoThreeSpectrum2479.graph fusedMap0128=true := by decide +kernel
theorem certified0128 : Certified (graph core0128) (root 8) 2 2 :=
  of_native_maps core0128 DegreeOneMiddleResidualSpectrum273.graph DegreeTwoThreeSpectrum2479.graph
    sourceMap0128 fusedMap0128 sourceMap0128_checked fusedMap0128_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0128
#print axioms sourceMap0128_checked
#print axioms fusedMap0128_checked
#print axioms certified0128
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
