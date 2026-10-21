/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1668 : Family 9 := level9.get ⟨426,by decide⟩
def sourceMap1668 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (sourceLabel 9 0 1 v)
def fusedMap1668 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1668_checked : acceptsGraphIso
    (source (graph core1668) (root 9) 0 1) DegreeOneSmallSpectrum1922.graph sourceMap1668=true := by decide +kernel
theorem fusedMap1668_checked : acceptsGraphIso
    (fused (graph core1668) (root 9) 0 1) DegreeOneSmallSpectrum1314.graph fusedMap1668=true := by decide +kernel
theorem certified1668 : Certified (graph core1668) (root 9) 0 1 :=
  of_native_maps core1668 DegreeOneSmallSpectrum1922.graph DegreeOneSmallSpectrum1314.graph
    sourceMap1668 fusedMap1668 sourceMap1668_checked fusedMap1668_checked
    DegreeOneSmallComparisons.comparison1668
#print axioms sourceMap1668_checked
#print axioms fusedMap1668_checked
#print axioms certified1668
def sourceMap1668swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 9 1 0 v)
def fusedMap1668swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1668swap_checked : acceptsGraphIso
    (source (graph core1668) (root 9) 1 0) DegreeOneSmallSpectrum1922.graph sourceMap1668swap=true := by decide +kernel
theorem fusedMap1668swap_checked : acceptsGraphIso
    (fused (graph core1668) (root 9) 1 0) DegreeOneSmallSpectrum1314.graph fusedMap1668swap=true := by decide +kernel
theorem certified1668swap : Certified (graph core1668) (root 9) 1 0 :=
  of_native_maps core1668 DegreeOneSmallSpectrum1922.graph DegreeOneSmallSpectrum1314.graph
    sourceMap1668swap fusedMap1668swap sourceMap1668swap_checked fusedMap1668swap_checked
    DegreeOneSmallComparisons.comparison1668
#print axioms sourceMap1668swap_checked
#print axioms fusedMap1668swap_checked
#print axioms certified1668swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
