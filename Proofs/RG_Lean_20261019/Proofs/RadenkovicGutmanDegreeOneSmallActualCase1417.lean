/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1417 : Family 9 := level9.get ⟨159,by decide⟩
def sourceMap1417 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 9 0 0 v)
def fusedMap1417 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1417_checked : acceptsGraphIso
    (source (graph core1417) (root 9) 0 0) DegreeOneSmallSpectrum700.graph sourceMap1417=true := by decide +kernel
theorem fusedMap1417_checked : acceptsGraphIso
    (fused (graph core1417) (root 9) 0 0) DegreeOneSmallSpectrum433.graph fusedMap1417=true := by decide +kernel
theorem certified1417 : Certified (graph core1417) (root 9) 0 0 :=
  of_native_maps core1417 DegreeOneSmallSpectrum700.graph DegreeOneSmallSpectrum433.graph
    sourceMap1417 fusedMap1417 sourceMap1417_checked fusedMap1417_checked
    DegreeOneSmallComparisons.comparison1417
#print axioms sourceMap1417_checked
#print axioms fusedMap1417_checked
#print axioms certified1417
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
