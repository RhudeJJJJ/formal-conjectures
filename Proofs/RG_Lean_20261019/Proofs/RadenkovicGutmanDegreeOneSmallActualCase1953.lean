/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1953 : Family 10 := level10.get ⟨255,by decide⟩
def sourceMap1953 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap1953 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1953_checked : acceptsGraphIso
    (source (graph core1953) (root 10) 0 0) DegreeOneSmallSpectrum1126.graph sourceMap1953=true := by decide +kernel
theorem fusedMap1953_checked : acceptsGraphIso
    (fused (graph core1953) (root 10) 0 0) DegreeOneSmallSpectrum1244.graph fusedMap1953=true := by decide +kernel
theorem certified1953 : Certified (graph core1953) (root 10) 0 0 :=
  of_native_maps core1953 DegreeOneSmallSpectrum1126.graph DegreeOneSmallSpectrum1244.graph
    sourceMap1953 fusedMap1953 sourceMap1953_checked fusedMap1953_checked
    DegreeOneSmallComparisons.comparison1953
#print axioms sourceMap1953_checked
#print axioms fusedMap1953_checked
#print axioms certified1953
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
