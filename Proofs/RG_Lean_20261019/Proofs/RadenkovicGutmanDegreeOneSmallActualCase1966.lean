/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1966 : Family 10 := level10.get ⟨284,by decide⟩
def sourceMap1966 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap1966 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1966_checked : acceptsGraphIso
    (source (graph core1966) (root 10) 0 0) DegreeOneSmallSpectrum1250.graph sourceMap1966=true := by decide +kernel
theorem fusedMap1966_checked : acceptsGraphIso
    (fused (graph core1966) (root 10) 0 0) DegreeOneSmallSpectrum1296.graph fusedMap1966=true := by decide +kernel
theorem certified1966 : Certified (graph core1966) (root 10) 0 0 :=
  of_native_maps core1966 DegreeOneSmallSpectrum1250.graph DegreeOneSmallSpectrum1296.graph
    sourceMap1966 fusedMap1966 sourceMap1966_checked fusedMap1966_checked
    DegreeOneSmallComparisons.comparison1966
#print axioms sourceMap1966_checked
#print axioms fusedMap1966_checked
#print axioms certified1966
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
