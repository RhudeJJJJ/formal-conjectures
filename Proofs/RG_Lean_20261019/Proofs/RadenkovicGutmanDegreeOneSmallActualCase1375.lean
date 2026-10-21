/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1375 : Family 9 := level9.get ⟨121,by decide⟩
def sourceMap1375 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,7,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1375 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap1375_checked : acceptsGraphIso
    (source (graph core1375) (root 9) 0 0) DegreeOneSmallSpectrum436.graph sourceMap1375=true := by decide +kernel
theorem fusedMap1375_checked : acceptsGraphIso
    (fused (graph core1375) (root 9) 0 0) DegreeOneSmallSpectrum581.graph fusedMap1375=true := by decide +kernel
theorem certified1375 : Certified (graph core1375) (root 9) 0 0 :=
  of_native_maps core1375 DegreeOneSmallSpectrum436.graph DegreeOneSmallSpectrum581.graph
    sourceMap1375 fusedMap1375 sourceMap1375_checked fusedMap1375_checked
    DegreeOneSmallComparisons.comparison1375
#print axioms sourceMap1375_checked
#print axioms fusedMap1375_checked
#print axioms certified1375
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
