/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1456 : Family 9 := level9.get ⟨189,by decide⟩
def sourceMap1456 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,10,11,12,9,7,8] (sourceLabel 9 0 1 v)
def fusedMap1456 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 0 1 v)
theorem sourceMap1456_checked : acceptsGraphIso
    (source (graph core1456) (root 9) 0 1) DegreeOneSmallSpectrum1267.graph sourceMap1456=true := by decide +kernel
theorem fusedMap1456_checked : acceptsGraphIso
    (fused (graph core1456) (root 9) 0 1) DegreeOneSmallSpectrum1290.graph fusedMap1456=true := by decide +kernel
theorem certified1456 : Certified (graph core1456) (root 9) 0 1 :=
  of_native_maps core1456 DegreeOneSmallSpectrum1267.graph DegreeOneSmallSpectrum1290.graph
    sourceMap1456 fusedMap1456 sourceMap1456_checked fusedMap1456_checked
    DegreeOneSmallComparisons.comparison1456
#print axioms sourceMap1456_checked
#print axioms fusedMap1456_checked
#print axioms certified1456
def sourceMap1456swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,10,11,12,7,8,9] (sourceLabel 9 1 0 v)
def fusedMap1456swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 1 0 v)
theorem sourceMap1456swap_checked : acceptsGraphIso
    (source (graph core1456) (root 9) 1 0) DegreeOneSmallSpectrum1267.graph sourceMap1456swap=true := by decide +kernel
theorem fusedMap1456swap_checked : acceptsGraphIso
    (fused (graph core1456) (root 9) 1 0) DegreeOneSmallSpectrum1290.graph fusedMap1456swap=true := by decide +kernel
theorem certified1456swap : Certified (graph core1456) (root 9) 1 0 :=
  of_native_maps core1456 DegreeOneSmallSpectrum1267.graph DegreeOneSmallSpectrum1290.graph
    sourceMap1456swap fusedMap1456swap sourceMap1456swap_checked fusedMap1456swap_checked
    DegreeOneSmallComparisons.comparison1456
#print axioms sourceMap1456swap_checked
#print axioms fusedMap1456swap_checked
#print axioms certified1456swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
