/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1353 : Family 9 := level9.get ⟨104,by decide⟩
def sourceMap1353 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1353 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1353_checked : acceptsGraphIso
    (source (graph core1353) (root 9) 0 0) DegreeOneSmallSpectrum468.graph sourceMap1353=true := by decide +kernel
theorem fusedMap1353_checked : acceptsGraphIso
    (fused (graph core1353) (root 9) 0 0) DegreeOneSmallSpectrum584.graph fusedMap1353=true := by decide +kernel
theorem certified1353 : Certified (graph core1353) (root 9) 0 0 :=
  of_native_maps core1353 DegreeOneSmallSpectrum468.graph DegreeOneSmallSpectrum584.graph
    sourceMap1353 fusedMap1353 sourceMap1353_checked fusedMap1353_checked
    DegreeOneSmallComparisons.comparison1353
#print axioms sourceMap1353_checked
#print axioms fusedMap1353_checked
#print axioms certified1353
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
