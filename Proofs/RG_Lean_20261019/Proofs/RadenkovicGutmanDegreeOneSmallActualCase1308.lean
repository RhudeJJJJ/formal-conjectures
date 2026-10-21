/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1308 : Family 9 := level9.get ⟨72,by decide⟩
def sourceMap1308 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1308 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1308_checked : acceptsGraphIso
    (source (graph core1308) (root 9) 0 1) DegreeOneSmallSpectrum1338.graph sourceMap1308=true := by decide +kernel
theorem fusedMap1308_checked : acceptsGraphIso
    (fused (graph core1308) (root 9) 0 1) DegreeOneSmallSpectrum914.graph fusedMap1308=true := by decide +kernel
theorem certified1308 : Certified (graph core1308) (root 9) 0 1 :=
  of_native_maps core1308 DegreeOneSmallSpectrum1338.graph DegreeOneSmallSpectrum914.graph
    sourceMap1308 fusedMap1308 sourceMap1308_checked fusedMap1308_checked
    DegreeOneSmallComparisons.comparison1308
#print axioms sourceMap1308_checked
#print axioms fusedMap1308_checked
#print axioms certified1308
def sourceMap1308swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1308swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1308swap_checked : acceptsGraphIso
    (source (graph core1308) (root 9) 1 0) DegreeOneSmallSpectrum1338.graph sourceMap1308swap=true := by decide +kernel
theorem fusedMap1308swap_checked : acceptsGraphIso
    (fused (graph core1308) (root 9) 1 0) DegreeOneSmallSpectrum914.graph fusedMap1308swap=true := by decide +kernel
theorem certified1308swap : Certified (graph core1308) (root 9) 1 0 :=
  of_native_maps core1308 DegreeOneSmallSpectrum1338.graph DegreeOneSmallSpectrum914.graph
    sourceMap1308swap fusedMap1308swap sourceMap1308swap_checked fusedMap1308swap_checked
    DegreeOneSmallComparisons.comparison1308
#print axioms sourceMap1308swap_checked
#print axioms fusedMap1308swap_checked
#print axioms certified1308swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
