/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1381 : Family 9 := level9.get ⟨127,by decide⟩
def sourceMap1381 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,5,6,7,3,4] (sourceLabel 9 0 0 v)
def fusedMap1381 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,5,6,7,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap1381_checked : acceptsGraphIso
    (source (graph core1381) (root 9) 0 0) DegreeOneSmallSpectrum429.graph sourceMap1381=true := by decide +kernel
theorem fusedMap1381_checked : acceptsGraphIso
    (fused (graph core1381) (root 9) 0 0) DegreeOneSmallSpectrum571.graph fusedMap1381=true := by decide +kernel
theorem certified1381 : Certified (graph core1381) (root 9) 0 0 :=
  of_native_maps core1381 DegreeOneSmallSpectrum429.graph DegreeOneSmallSpectrum571.graph
    sourceMap1381 fusedMap1381 sourceMap1381_checked fusedMap1381_checked
    DegreeOneSmallComparisons.comparison1381
#print axioms sourceMap1381_checked
#print axioms fusedMap1381_checked
#print axioms certified1381
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
