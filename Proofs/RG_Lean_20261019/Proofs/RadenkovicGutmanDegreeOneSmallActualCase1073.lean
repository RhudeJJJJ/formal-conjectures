/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1073 : Family 8 := level8.get ⟨136,by decide⟩
def sourceMap1073 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1073 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1073_checked : acceptsGraphIso
    (source (graph core1073) (root 8) 0 2) DegreeOneSmallSpectrum1318.graph sourceMap1073=true := by decide +kernel
theorem fusedMap1073_checked : acceptsGraphIso
    (fused (graph core1073) (root 8) 0 2) DegreeOneSmallSpectrum1319.graph fusedMap1073=true := by decide +kernel
theorem certified1073 : Certified (graph core1073) (root 8) 0 2 :=
  of_native_maps core1073 DegreeOneSmallSpectrum1318.graph DegreeOneSmallSpectrum1319.graph
    sourceMap1073 fusedMap1073 sourceMap1073_checked fusedMap1073_checked
    DegreeOneSmallComparisons.comparison1073
#print axioms sourceMap1073_checked
#print axioms fusedMap1073_checked
#print axioms certified1073
def sourceMap1073swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1073swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1073swap_checked : acceptsGraphIso
    (source (graph core1073) (root 8) 2 0) DegreeOneSmallSpectrum1318.graph sourceMap1073swap=true := by decide +kernel
theorem fusedMap1073swap_checked : acceptsGraphIso
    (fused (graph core1073) (root 8) 2 0) DegreeOneSmallSpectrum1319.graph fusedMap1073swap=true := by decide +kernel
theorem certified1073swap : Certified (graph core1073) (root 8) 2 0 :=
  of_native_maps core1073 DegreeOneSmallSpectrum1318.graph DegreeOneSmallSpectrum1319.graph
    sourceMap1073swap fusedMap1073swap sourceMap1073swap_checked fusedMap1073swap_checked
    DegreeOneSmallComparisons.comparison1073
#print axioms sourceMap1073swap_checked
#print axioms fusedMap1073swap_checked
#print axioms certified1073swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
