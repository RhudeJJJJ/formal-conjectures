/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1107 : Family 10 := level10.get ⟨1187,by decide⟩
def sourceMap1107 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1107 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1107_checked : acceptsGraphIso
    (source (graph core1107) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2111.graph sourceMap1107=true := by decide +kernel
theorem fusedMap1107_checked : acceptsGraphIso
    (fused (graph core1107) (root 10) 2 2) DegreeTwoThreeSpectrum6359.graph fusedMap1107=true := by decide +kernel
theorem certified1107 : Certified (graph core1107) (root 10) 2 2 :=
  of_native_maps core1107 DegreeOneMiddleResidualSpectrum2111.graph DegreeTwoThreeSpectrum6359.graph
    sourceMap1107 fusedMap1107 sourceMap1107_checked fusedMap1107_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1107
#print axioms sourceMap1107_checked
#print axioms fusedMap1107_checked
#print axioms certified1107
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
