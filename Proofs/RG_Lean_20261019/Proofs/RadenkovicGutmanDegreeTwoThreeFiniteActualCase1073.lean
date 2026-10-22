/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1073 : Family 7 := level7.get ⟨53,by decide⟩
def sourceMap1073 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 7 0 2 v)
def fusedMap1073 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (fusedLabel 7 0 2 v)
theorem sourceMap1073_checked : acceptsGraphIso
    (source (graph core1073) (root 7) 0 2) DegreeOneSmallSpectrum573.graph sourceMap1073=true := by decide +kernel
theorem fusedMap1073_checked : acceptsGraphIso
    (fused (graph core1073) (root 7) 0 2) DegreeOneSmallSpectrum575.graph fusedMap1073=true := by decide +kernel
theorem certified1073 : Certified (graph core1073) (root 7) 0 2 :=
  of_native_maps core1073 DegreeOneSmallSpectrum573.graph DegreeOneSmallSpectrum575.graph
    sourceMap1073 fusedMap1073 sourceMap1073_checked fusedMap1073_checked
    DegreeTwoThreeFiniteComparisons.comparison1073
#print axioms sourceMap1073_checked
#print axioms fusedMap1073_checked
#print axioms certified1073
def sourceMap1073swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9,11] (sourceLabel 7 2 0 v)
def fusedMap1073swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (fusedLabel 7 2 0 v)
theorem sourceMap1073swap_checked : acceptsGraphIso
    (source (graph core1073) (root 7) 2 0) DegreeOneSmallSpectrum573.graph sourceMap1073swap=true := by decide +kernel
theorem fusedMap1073swap_checked : acceptsGraphIso
    (fused (graph core1073) (root 7) 2 0) DegreeOneSmallSpectrum575.graph fusedMap1073swap=true := by decide +kernel
theorem certified1073swap : Certified (graph core1073) (root 7) 2 0 :=
  of_native_maps core1073 DegreeOneSmallSpectrum573.graph DegreeOneSmallSpectrum575.graph
    sourceMap1073swap fusedMap1073swap sourceMap1073swap_checked fusedMap1073swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1073
#print axioms sourceMap1073swap_checked
#print axioms fusedMap1073swap_checked
#print axioms certified1073swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
