/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1137 : Family 10 := level10.get ⟨1305,by decide⟩
def sourceMap1137 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1137 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1137_checked : acceptsGraphIso
    (source (graph core1137) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2192.graph sourceMap1137=true := by decide +kernel
theorem fusedMap1137_checked : acceptsGraphIso
    (fused (graph core1137) (root 10) 2 2) DegreeTwoThreeSpectrum6599.graph fusedMap1137=true := by decide +kernel
theorem certified1137 : Certified (graph core1137) (root 10) 2 2 :=
  of_native_maps core1137 DegreeOneMiddleResidualSpectrum2192.graph DegreeTwoThreeSpectrum6599.graph
    sourceMap1137 fusedMap1137 sourceMap1137_checked fusedMap1137_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1137
#print axioms sourceMap1137_checked
#print axioms fusedMap1137_checked
#print axioms certified1137
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
