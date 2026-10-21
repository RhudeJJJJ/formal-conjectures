/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1611 : Family 9 := level9.get ⟨355,by decide⟩
def sourceMap1611 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 9 0 0 v)
def fusedMap1611 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1611_checked : acceptsGraphIso
    (source (graph core1611) (root 9) 0 0) DegreeOneSmallSpectrum678.graph sourceMap1611=true := by decide +kernel
theorem fusedMap1611_checked : acceptsGraphIso
    (fused (graph core1611) (root 9) 0 0) DegreeOneSmallSpectrum683.graph fusedMap1611=true := by decide +kernel
theorem certified1611 : Certified (graph core1611) (root 9) 0 0 :=
  of_native_maps core1611 DegreeOneSmallSpectrum678.graph DegreeOneSmallSpectrum683.graph
    sourceMap1611 fusedMap1611 sourceMap1611_checked fusedMap1611_checked
    DegreeOneSmallComparisons.comparison1611
#print axioms sourceMap1611_checked
#print axioms fusedMap1611_checked
#print axioms certified1611
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
