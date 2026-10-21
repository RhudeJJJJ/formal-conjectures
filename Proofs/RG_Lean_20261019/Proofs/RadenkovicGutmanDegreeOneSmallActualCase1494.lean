/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1494 : Family 9 := level9.get ⟨226,by decide⟩
def sourceMap1494 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1494 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1494_checked : acceptsGraphIso
    (source (graph core1494) (root 9) 0 1) DegreeOneSmallSpectrum1396.graph sourceMap1494=true := by decide +kernel
theorem fusedMap1494_checked : acceptsGraphIso
    (fused (graph core1494) (root 9) 0 1) DegreeOneSmallSpectrum1398.graph fusedMap1494=true := by decide +kernel
theorem certified1494 : Certified (graph core1494) (root 9) 0 1 :=
  of_native_maps core1494 DegreeOneSmallSpectrum1396.graph DegreeOneSmallSpectrum1398.graph
    sourceMap1494 fusedMap1494 sourceMap1494_checked fusedMap1494_checked
    DegreeOneSmallComparisons.comparison1494
#print axioms sourceMap1494_checked
#print axioms fusedMap1494_checked
#print axioms certified1494
def sourceMap1494swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1494swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1494swap_checked : acceptsGraphIso
    (source (graph core1494) (root 9) 1 0) DegreeOneSmallSpectrum1396.graph sourceMap1494swap=true := by decide +kernel
theorem fusedMap1494swap_checked : acceptsGraphIso
    (fused (graph core1494) (root 9) 1 0) DegreeOneSmallSpectrum1398.graph fusedMap1494swap=true := by decide +kernel
theorem certified1494swap : Certified (graph core1494) (root 9) 1 0 :=
  of_native_maps core1494 DegreeOneSmallSpectrum1396.graph DegreeOneSmallSpectrum1398.graph
    sourceMap1494swap fusedMap1494swap sourceMap1494swap_checked fusedMap1494swap_checked
    DegreeOneSmallComparisons.comparison1494
#print axioms sourceMap1494swap_checked
#print axioms fusedMap1494swap_checked
#print axioms certified1494swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
