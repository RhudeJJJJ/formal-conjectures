/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1565 : Family 9 := level9.get ⟨295,by decide⟩
def sourceMap1565 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,9,10,11,5,6,7,8,3,4] (sourceLabel 9 0 0 v)
def fusedMap1565 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,4,5,6,7,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap1565_checked : acceptsGraphIso
    (source (graph core1565) (root 9) 0 0) DegreeOneSmallSpectrum687.graph sourceMap1565=true := by decide +kernel
theorem fusedMap1565_checked : acceptsGraphIso
    (fused (graph core1565) (root 9) 0 0) DegreeOneSmallSpectrum568.graph fusedMap1565=true := by decide +kernel
theorem certified1565 : Certified (graph core1565) (root 9) 0 0 :=
  of_native_maps core1565 DegreeOneSmallSpectrum687.graph DegreeOneSmallSpectrum568.graph
    sourceMap1565 fusedMap1565 sourceMap1565_checked fusedMap1565_checked
    DegreeOneSmallComparisons.comparison1565
#print axioms sourceMap1565_checked
#print axioms fusedMap1565_checked
#print axioms certified1565
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
