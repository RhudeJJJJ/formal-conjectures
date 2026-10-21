/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1361 : Family 9 := level9.get ⟨112,by decide⟩
def sourceMap1361 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,5,6,7,3,4] (sourceLabel 9 0 0 v)
def fusedMap1361 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap1361_checked : acceptsGraphIso
    (source (graph core1361) (root 9) 0 0) DegreeOneSmallSpectrum458.graph sourceMap1361=true := by decide +kernel
theorem fusedMap1361_checked : acceptsGraphIso
    (fused (graph core1361) (root 9) 0 0) DegreeOneSmallSpectrum585.graph fusedMap1361=true := by decide +kernel
theorem certified1361 : Certified (graph core1361) (root 9) 0 0 :=
  of_native_maps core1361 DegreeOneSmallSpectrum458.graph DegreeOneSmallSpectrum585.graph
    sourceMap1361 fusedMap1361 sourceMap1361_checked fusedMap1361_checked
    DegreeOneSmallComparisons.comparison1361
#print axioms sourceMap1361_checked
#print axioms fusedMap1361_checked
#print axioms certified1361
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
