/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1252 : Family 9 := level9.get ⟨32,by decide⟩
def sourceMap1252 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1252 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (fusedLabel 9 0 1 v)
theorem sourceMap1252_checked : acceptsGraphIso
    (source (graph core1252) (root 9) 0 1) DegreeOneSmallSpectrum928.graph sourceMap1252=true := by decide +kernel
theorem fusedMap1252_checked : acceptsGraphIso
    (fused (graph core1252) (root 9) 0 1) DegreeOneSmallSpectrum975.graph fusedMap1252=true := by decide +kernel
theorem certified1252 : Certified (graph core1252) (root 9) 0 1 :=
  of_native_maps core1252 DegreeOneSmallSpectrum928.graph DegreeOneSmallSpectrum975.graph
    sourceMap1252 fusedMap1252 sourceMap1252_checked fusedMap1252_checked
    DegreeOneSmallComparisons.comparison1252
#print axioms sourceMap1252_checked
#print axioms fusedMap1252_checked
#print axioms certified1252
def sourceMap1252swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1252swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (fusedLabel 9 1 0 v)
theorem sourceMap1252swap_checked : acceptsGraphIso
    (source (graph core1252) (root 9) 1 0) DegreeOneSmallSpectrum928.graph sourceMap1252swap=true := by decide +kernel
theorem fusedMap1252swap_checked : acceptsGraphIso
    (fused (graph core1252) (root 9) 1 0) DegreeOneSmallSpectrum975.graph fusedMap1252swap=true := by decide +kernel
theorem certified1252swap : Certified (graph core1252) (root 9) 1 0 :=
  of_native_maps core1252 DegreeOneSmallSpectrum928.graph DegreeOneSmallSpectrum975.graph
    sourceMap1252swap fusedMap1252swap sourceMap1252swap_checked fusedMap1252swap_checked
    DegreeOneSmallComparisons.comparison1252
#print axioms sourceMap1252swap_checked
#print axioms fusedMap1252swap_checked
#print axioms certified1252swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
