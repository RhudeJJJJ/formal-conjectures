/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1940 : Family 10 := level10.get ⟨236,by decide⟩
def sourceMap1940 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap1940 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1940_checked : acceptsGraphIso
    (source (graph core1940) (root 10) 0 0) DegreeOneSmallSpectrum1125.graph sourceMap1940=true := by decide +kernel
theorem fusedMap1940_checked : acceptsGraphIso
    (fused (graph core1940) (root 10) 0 0) DegreeOneSmallSpectrum1179.graph fusedMap1940=true := by decide +kernel
theorem certified1940 : Certified (graph core1940) (root 10) 0 0 :=
  of_native_maps core1940 DegreeOneSmallSpectrum1125.graph DegreeOneSmallSpectrum1179.graph
    sourceMap1940 fusedMap1940 sourceMap1940_checked fusedMap1940_checked
    DegreeOneSmallComparisons.comparison1940
#print axioms sourceMap1940_checked
#print axioms fusedMap1940_checked
#print axioms certified1940
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
