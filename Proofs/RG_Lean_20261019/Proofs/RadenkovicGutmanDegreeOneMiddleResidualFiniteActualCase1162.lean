/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1162 : Family 10 := level10.get ⟨1417,by decide⟩
def sourceMap1162 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap1162 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1162_checked : acceptsGraphIso
    (source (graph core1162) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2267.graph sourceMap1162=true := by decide +kernel
theorem fusedMap1162_checked : acceptsGraphIso
    (fused (graph core1162) (root 10) 2 2) DegreeTwoThreeSpectrum6867.graph fusedMap1162=true := by decide +kernel
theorem certified1162 : Certified (graph core1162) (root 10) 2 2 :=
  of_native_maps core1162 DegreeOneMiddleResidualSpectrum2267.graph DegreeTwoThreeSpectrum6867.graph
    sourceMap1162 fusedMap1162 sourceMap1162_checked fusedMap1162_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1162
#print axioms sourceMap1162_checked
#print axioms fusedMap1162_checked
#print axioms certified1162
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
