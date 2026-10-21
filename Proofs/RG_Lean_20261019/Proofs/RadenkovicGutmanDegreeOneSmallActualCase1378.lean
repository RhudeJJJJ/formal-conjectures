/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1378 : Family 9 := level9.get ⟨125,by decide⟩
def sourceMap1378 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1378 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (fusedLabel 9 0 1 v)
theorem sourceMap1378_checked : acceptsGraphIso
    (source (graph core1378) (root 9) 0 1) DegreeOneSmallSpectrum1398.graph sourceMap1378=true := by decide +kernel
theorem fusedMap1378_checked : acceptsGraphIso
    (fused (graph core1378) (root 9) 0 1) DegreeOneSmallSpectrum967.graph fusedMap1378=true := by decide +kernel
theorem certified1378 : Certified (graph core1378) (root 9) 0 1 :=
  of_native_maps core1378 DegreeOneSmallSpectrum1398.graph DegreeOneSmallSpectrum967.graph
    sourceMap1378 fusedMap1378 sourceMap1378_checked fusedMap1378_checked
    DegreeOneSmallComparisons.comparison1378
#print axioms sourceMap1378_checked
#print axioms fusedMap1378_checked
#print axioms certified1378
def sourceMap1378swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1378swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (fusedLabel 9 1 0 v)
theorem sourceMap1378swap_checked : acceptsGraphIso
    (source (graph core1378) (root 9) 1 0) DegreeOneSmallSpectrum1398.graph sourceMap1378swap=true := by decide +kernel
theorem fusedMap1378swap_checked : acceptsGraphIso
    (fused (graph core1378) (root 9) 1 0) DegreeOneSmallSpectrum967.graph fusedMap1378swap=true := by decide +kernel
theorem certified1378swap : Certified (graph core1378) (root 9) 1 0 :=
  of_native_maps core1378 DegreeOneSmallSpectrum1398.graph DegreeOneSmallSpectrum967.graph
    sourceMap1378swap fusedMap1378swap sourceMap1378swap_checked fusedMap1378swap_checked
    DegreeOneSmallComparisons.comparison1378
#print axioms sourceMap1378swap_checked
#print axioms fusedMap1378swap_checked
#print axioms certified1378swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
