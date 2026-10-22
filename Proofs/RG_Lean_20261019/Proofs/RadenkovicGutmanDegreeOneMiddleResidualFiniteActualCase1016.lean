/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1016 : Family 10 := level10.get ⟨933,by decide⟩
def sourceMap1016 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1016 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1016_checked : acceptsGraphIso
    (source (graph core1016) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2319.graph sourceMap1016=true := by decide +kernel
theorem fusedMap1016_checked : acceptsGraphIso
    (fused (graph core1016) (root 10) 2 2) DegreeTwoThreeSpectrum5828.graph fusedMap1016=true := by decide +kernel
theorem certified1016 : Certified (graph core1016) (root 10) 2 2 :=
  of_native_maps core1016 DegreeOneMiddleResidualSpectrum2319.graph DegreeTwoThreeSpectrum5828.graph
    sourceMap1016 fusedMap1016 sourceMap1016_checked fusedMap1016_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1016
#print axioms sourceMap1016_checked
#print axioms fusedMap1016_checked
#print axioms certified1016
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
