/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1511 : Family 9 := level9.get ⟨240,by decide⟩
def sourceMap1511 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,5,6,7,3,4] (sourceLabel 9 0 0 v)
def fusedMap1511 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1511_checked : acceptsGraphIso
    (source (graph core1511) (root 9) 0 0) DegreeOneSmallSpectrum682.graph sourceMap1511=true := by decide +kernel
theorem fusedMap1511_checked : acceptsGraphIso
    (fused (graph core1511) (root 9) 0 0) DegreeOneSmallSpectrum553.graph fusedMap1511=true := by decide +kernel
theorem certified1511 : Certified (graph core1511) (root 9) 0 0 :=
  of_native_maps core1511 DegreeOneSmallSpectrum682.graph DegreeOneSmallSpectrum553.graph
    sourceMap1511 fusedMap1511 sourceMap1511_checked fusedMap1511_checked
    DegreeOneSmallComparisons.comparison1511
#print axioms sourceMap1511_checked
#print axioms fusedMap1511_checked
#print axioms certified1511
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
