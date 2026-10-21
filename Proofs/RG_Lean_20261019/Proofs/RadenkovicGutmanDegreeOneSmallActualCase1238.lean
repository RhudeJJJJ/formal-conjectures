/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1238 : Family 9 := level9.get ⟨24,by decide⟩
def sourceMap1238 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1238 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1238_checked : acceptsGraphIso
    (source (graph core1238) (root 9) 0 1) DegreeOneSmallSpectrum938.graph sourceMap1238=true := by decide +kernel
theorem fusedMap1238_checked : acceptsGraphIso
    (fused (graph core1238) (root 9) 0 1) DegreeOneSmallSpectrum956.graph fusedMap1238=true := by decide +kernel
theorem certified1238 : Certified (graph core1238) (root 9) 0 1 :=
  of_native_maps core1238 DegreeOneSmallSpectrum938.graph DegreeOneSmallSpectrum956.graph
    sourceMap1238 fusedMap1238 sourceMap1238_checked fusedMap1238_checked
    DegreeOneSmallComparisons.comparison1238
#print axioms sourceMap1238_checked
#print axioms fusedMap1238_checked
#print axioms certified1238
def sourceMap1238swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1238swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1238swap_checked : acceptsGraphIso
    (source (graph core1238) (root 9) 1 0) DegreeOneSmallSpectrum938.graph sourceMap1238swap=true := by decide +kernel
theorem fusedMap1238swap_checked : acceptsGraphIso
    (fused (graph core1238) (root 9) 1 0) DegreeOneSmallSpectrum956.graph fusedMap1238swap=true := by decide +kernel
theorem certified1238swap : Certified (graph core1238) (root 9) 1 0 :=
  of_native_maps core1238 DegreeOneSmallSpectrum938.graph DegreeOneSmallSpectrum956.graph
    sourceMap1238swap fusedMap1238swap sourceMap1238swap_checked fusedMap1238swap_checked
    DegreeOneSmallComparisons.comparison1238
#print axioms sourceMap1238swap_checked
#print axioms fusedMap1238swap_checked
#print axioms certified1238swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
