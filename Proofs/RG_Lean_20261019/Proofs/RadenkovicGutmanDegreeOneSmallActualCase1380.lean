/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1380 : Family 9 := level9.get ⟨126,by decide⟩
def sourceMap1380 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1380 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (fusedLabel 9 0 1 v)
theorem sourceMap1380_checked : acceptsGraphIso
    (source (graph core1380) (root 9) 0 1) DegreeOneSmallSpectrum1403.graph sourceMap1380=true := by decide +kernel
theorem fusedMap1380_checked : acceptsGraphIso
    (fused (graph core1380) (root 9) 0 1) DegreeOneSmallSpectrum968.graph fusedMap1380=true := by decide +kernel
theorem certified1380 : Certified (graph core1380) (root 9) 0 1 :=
  of_native_maps core1380 DegreeOneSmallSpectrum1403.graph DegreeOneSmallSpectrum968.graph
    sourceMap1380 fusedMap1380 sourceMap1380_checked fusedMap1380_checked
    DegreeOneSmallComparisons.comparison1380
#print axioms sourceMap1380_checked
#print axioms fusedMap1380_checked
#print axioms certified1380
def sourceMap1380swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1380swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (fusedLabel 9 1 0 v)
theorem sourceMap1380swap_checked : acceptsGraphIso
    (source (graph core1380) (root 9) 1 0) DegreeOneSmallSpectrum1403.graph sourceMap1380swap=true := by decide +kernel
theorem fusedMap1380swap_checked : acceptsGraphIso
    (fused (graph core1380) (root 9) 1 0) DegreeOneSmallSpectrum968.graph fusedMap1380swap=true := by decide +kernel
theorem certified1380swap : Certified (graph core1380) (root 9) 1 0 :=
  of_native_maps core1380 DegreeOneSmallSpectrum1403.graph DegreeOneSmallSpectrum968.graph
    sourceMap1380swap fusedMap1380swap sourceMap1380swap_checked fusedMap1380swap_checked
    DegreeOneSmallComparisons.comparison1380
#print axioms sourceMap1380swap_checked
#print axioms fusedMap1380swap_checked
#print axioms certified1380swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
