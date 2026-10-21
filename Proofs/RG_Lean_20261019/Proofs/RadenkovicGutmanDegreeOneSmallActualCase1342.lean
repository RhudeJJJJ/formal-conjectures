/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1342 : Family 9 := level9.get ⟨96,by decide⟩
def sourceMap1342 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1342 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1342_checked : acceptsGraphIso
    (source (graph core1342) (root 9) 0 1) DegreeOneSmallSpectrum1446.graph sourceMap1342=true := by decide +kernel
theorem fusedMap1342_checked : acceptsGraphIso
    (fused (graph core1342) (root 9) 0 1) DegreeOneSmallSpectrum948.graph fusedMap1342=true := by decide +kernel
theorem certified1342 : Certified (graph core1342) (root 9) 0 1 :=
  of_native_maps core1342 DegreeOneSmallSpectrum1446.graph DegreeOneSmallSpectrum948.graph
    sourceMap1342 fusedMap1342 sourceMap1342_checked fusedMap1342_checked
    DegreeOneSmallComparisons.comparison1342
#print axioms sourceMap1342_checked
#print axioms fusedMap1342_checked
#print axioms certified1342
def sourceMap1342swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1342swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1342swap_checked : acceptsGraphIso
    (source (graph core1342) (root 9) 1 0) DegreeOneSmallSpectrum1446.graph sourceMap1342swap=true := by decide +kernel
theorem fusedMap1342swap_checked : acceptsGraphIso
    (fused (graph core1342) (root 9) 1 0) DegreeOneSmallSpectrum948.graph fusedMap1342swap=true := by decide +kernel
theorem certified1342swap : Certified (graph core1342) (root 9) 1 0 :=
  of_native_maps core1342 DegreeOneSmallSpectrum1446.graph DegreeOneSmallSpectrum948.graph
    sourceMap1342swap fusedMap1342swap sourceMap1342swap_checked fusedMap1342swap_checked
    DegreeOneSmallComparisons.comparison1342
#print axioms sourceMap1342swap_checked
#print axioms fusedMap1342swap_checked
#print axioms certified1342swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
