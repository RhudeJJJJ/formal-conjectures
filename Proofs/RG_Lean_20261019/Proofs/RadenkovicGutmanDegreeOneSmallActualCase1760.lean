/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1760 : Family 9 := level9.get ⟨630,by decide⟩
def sourceMap1760 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1760 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1760_checked : acceptsGraphIso
    (source (graph core1760) (root 9) 0 1) DegreeOneSmallSpectrum1889.graph sourceMap1760=true := by decide +kernel
theorem fusedMap1760_checked : acceptsGraphIso
    (fused (graph core1760) (root 9) 0 1) DegreeOneSmallSpectrum1890.graph fusedMap1760=true := by decide +kernel
theorem certified1760 : Certified (graph core1760) (root 9) 0 1 :=
  of_native_maps core1760 DegreeOneSmallSpectrum1889.graph DegreeOneSmallSpectrum1890.graph
    sourceMap1760 fusedMap1760 sourceMap1760_checked fusedMap1760_checked
    DegreeOneSmallComparisons.comparison1760
#print axioms sourceMap1760_checked
#print axioms fusedMap1760_checked
#print axioms certified1760
def sourceMap1760swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1760swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1760swap_checked : acceptsGraphIso
    (source (graph core1760) (root 9) 1 0) DegreeOneSmallSpectrum1889.graph sourceMap1760swap=true := by decide +kernel
theorem fusedMap1760swap_checked : acceptsGraphIso
    (fused (graph core1760) (root 9) 1 0) DegreeOneSmallSpectrum1890.graph fusedMap1760swap=true := by decide +kernel
theorem certified1760swap : Certified (graph core1760) (root 9) 1 0 :=
  of_native_maps core1760 DegreeOneSmallSpectrum1889.graph DegreeOneSmallSpectrum1890.graph
    sourceMap1760swap fusedMap1760swap sourceMap1760swap_checked fusedMap1760swap_checked
    DegreeOneSmallComparisons.comparison1760
#print axioms sourceMap1760swap_checked
#print axioms fusedMap1760swap_checked
#print axioms certified1760swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
