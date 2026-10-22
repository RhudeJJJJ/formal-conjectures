/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1056 : Family 10 := level10.get ⟨1049,by decide⟩
def sourceMap1056 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1056 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1056_checked : acceptsGraphIso
    (source (graph core1056) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2005.graph sourceMap1056=true := by decide +kernel
theorem fusedMap1056_checked : acceptsGraphIso
    (fused (graph core1056) (root 10) 2 2) DegreeTwoThreeSpectrum6083.graph fusedMap1056=true := by decide +kernel
theorem certified1056 : Certified (graph core1056) (root 10) 2 2 :=
  of_native_maps core1056 DegreeOneMiddleResidualSpectrum2005.graph DegreeTwoThreeSpectrum6083.graph
    sourceMap1056 fusedMap1056 sourceMap1056_checked fusedMap1056_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1056
#print axioms sourceMap1056_checked
#print axioms fusedMap1056_checked
#print axioms certified1056
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
