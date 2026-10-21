/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1367 : Family 9 := level9.get ⟨115,by decide⟩
def sourceMap1367 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,6,7,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1367 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap1367_checked : acceptsGraphIso
    (source (graph core1367) (root 9) 0 0) DegreeOneSmallSpectrum441.graph sourceMap1367=true := by decide +kernel
theorem fusedMap1367_checked : acceptsGraphIso
    (fused (graph core1367) (root 9) 0 0) DegreeOneSmallSpectrum583.graph fusedMap1367=true := by decide +kernel
theorem certified1367 : Certified (graph core1367) (root 9) 0 0 :=
  of_native_maps core1367 DegreeOneSmallSpectrum441.graph DegreeOneSmallSpectrum583.graph
    sourceMap1367 fusedMap1367 sourceMap1367_checked fusedMap1367_checked
    DegreeOneSmallComparisons.comparison1367
#print axioms sourceMap1367_checked
#print axioms fusedMap1367_checked
#print axioms certified1367
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
