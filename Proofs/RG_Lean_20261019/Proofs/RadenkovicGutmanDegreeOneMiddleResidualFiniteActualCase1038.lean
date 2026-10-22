/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1038 : Family 10 := level10.get ⟨1013,by decide⟩
def sourceMap1038 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1038 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1038_checked : acceptsGraphIso
    (source (graph core1038) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1974.graph sourceMap1038=true := by decide +kernel
theorem fusedMap1038_checked : acceptsGraphIso
    (fused (graph core1038) (root 10) 2 2) DegreeTwoThreeSpectrum6007.graph fusedMap1038=true := by decide +kernel
theorem certified1038 : Certified (graph core1038) (root 10) 2 2 :=
  of_native_maps core1038 DegreeOneMiddleResidualSpectrum1974.graph DegreeTwoThreeSpectrum6007.graph
    sourceMap1038 fusedMap1038 sourceMap1038_checked fusedMap1038_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1038
#print axioms sourceMap1038_checked
#print axioms fusedMap1038_checked
#print axioms certified1038
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
