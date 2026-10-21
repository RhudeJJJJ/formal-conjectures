/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1957 : Family 10 := level10.get ⟨262,by decide⟩
def sourceMap1957 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap1957 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap1957_checked : acceptsGraphIso
    (source (graph core1957) (root 10) 0 0) DegreeOneSmallSpectrum1139.graph sourceMap1957=true := by decide +kernel
theorem fusedMap1957_checked : acceptsGraphIso
    (fused (graph core1957) (root 10) 0 0) DegreeOneSmallSpectrum1286.graph fusedMap1957=true := by decide +kernel
theorem certified1957 : Certified (graph core1957) (root 10) 0 0 :=
  of_native_maps core1957 DegreeOneSmallSpectrum1139.graph DegreeOneSmallSpectrum1286.graph
    sourceMap1957 fusedMap1957 sourceMap1957_checked fusedMap1957_checked
    DegreeOneSmallComparisons.comparison1957
#print axioms sourceMap1957_checked
#print axioms fusedMap1957_checked
#print axioms certified1957
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
