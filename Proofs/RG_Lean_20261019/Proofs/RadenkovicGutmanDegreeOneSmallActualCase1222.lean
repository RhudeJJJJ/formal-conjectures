/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1222 : Family 9 := level9.get ⟨14,by decide⟩
def sourceMap1222 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1222 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1222_checked : acceptsGraphIso
    (source (graph core1222) (root 9) 0 1) DegreeOneSmallSpectrum898.graph sourceMap1222=true := by decide +kernel
theorem fusedMap1222_checked : acceptsGraphIso
    (fused (graph core1222) (root 9) 0 1) DegreeOneSmallSpectrum907.graph fusedMap1222=true := by decide +kernel
theorem certified1222 : Certified (graph core1222) (root 9) 0 1 :=
  of_native_maps core1222 DegreeOneSmallSpectrum898.graph DegreeOneSmallSpectrum907.graph
    sourceMap1222 fusedMap1222 sourceMap1222_checked fusedMap1222_checked
    DegreeOneSmallComparisons.comparison1222
#print axioms sourceMap1222_checked
#print axioms fusedMap1222_checked
#print axioms certified1222
def sourceMap1222swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1222swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1222swap_checked : acceptsGraphIso
    (source (graph core1222) (root 9) 1 0) DegreeOneSmallSpectrum898.graph sourceMap1222swap=true := by decide +kernel
theorem fusedMap1222swap_checked : acceptsGraphIso
    (fused (graph core1222) (root 9) 1 0) DegreeOneSmallSpectrum907.graph fusedMap1222swap=true := by decide +kernel
theorem certified1222swap : Certified (graph core1222) (root 9) 1 0 :=
  of_native_maps core1222 DegreeOneSmallSpectrum898.graph DegreeOneSmallSpectrum907.graph
    sourceMap1222swap fusedMap1222swap sourceMap1222swap_checked fusedMap1222swap_checked
    DegreeOneSmallComparisons.comparison1222
#print axioms sourceMap1222swap_checked
#print axioms fusedMap1222swap_checked
#print axioms certified1222swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
