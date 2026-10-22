/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1028 : Family 10 := level10.get ⟨997,by decide⟩
def sourceMap1028 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1028 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1028_checked : acceptsGraphIso
    (source (graph core1028) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1959.graph sourceMap1028=true := by decide +kernel
theorem fusedMap1028_checked : acceptsGraphIso
    (fused (graph core1028) (root 10) 2 2) DegreeTwoThreeSpectrum5968.graph fusedMap1028=true := by decide +kernel
theorem certified1028 : Certified (graph core1028) (root 10) 2 2 :=
  of_native_maps core1028 DegreeOneMiddleResidualSpectrum1959.graph DegreeTwoThreeSpectrum5968.graph
    sourceMap1028 fusedMap1028 sourceMap1028_checked fusedMap1028_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1028
#print axioms sourceMap1028_checked
#print axioms fusedMap1028_checked
#print axioms certified1028
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
