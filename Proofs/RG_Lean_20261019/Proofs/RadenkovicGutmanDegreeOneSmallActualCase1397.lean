/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1397 : Family 9 := level9.get ⟨144,by decide⟩
def sourceMap1397 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 9 0 0 v)
def fusedMap1397 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1397_checked : acceptsGraphIso
    (source (graph core1397) (root 9) 0 0) DegreeOneSmallSpectrum653.graph sourceMap1397=true := by decide +kernel
theorem fusedMap1397_checked : acceptsGraphIso
    (fused (graph core1397) (root 9) 0 0) DegreeOneSmallSpectrum407.graph fusedMap1397=true := by decide +kernel
theorem certified1397 : Certified (graph core1397) (root 9) 0 0 :=
  of_native_maps core1397 DegreeOneSmallSpectrum653.graph DegreeOneSmallSpectrum407.graph
    sourceMap1397 fusedMap1397 sourceMap1397_checked fusedMap1397_checked
    DegreeOneSmallComparisons.comparison1397
#print axioms sourceMap1397_checked
#print axioms fusedMap1397_checked
#print axioms certified1397
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
