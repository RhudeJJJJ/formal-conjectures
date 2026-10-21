/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1636 : Family 9 := level9.get ⟨376,by decide⟩
def sourceMap1636 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (sourceLabel 9 0 1 v)
def fusedMap1636 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1636_checked : acceptsGraphIso
    (source (graph core1636) (root 9) 0 1) DegreeOneSmallSpectrum1831.graph sourceMap1636=true := by decide +kernel
theorem fusedMap1636_checked : acceptsGraphIso
    (fused (graph core1636) (root 9) 0 1) DegreeOneSmallSpectrum1138.graph fusedMap1636=true := by decide +kernel
theorem certified1636 : Certified (graph core1636) (root 9) 0 1 :=
  of_native_maps core1636 DegreeOneSmallSpectrum1831.graph DegreeOneSmallSpectrum1138.graph
    sourceMap1636 fusedMap1636 sourceMap1636_checked fusedMap1636_checked
    DegreeOneSmallComparisons.comparison1636
#print axioms sourceMap1636_checked
#print axioms fusedMap1636_checked
#print axioms certified1636
def sourceMap1636swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 9 1 0 v)
def fusedMap1636swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1636swap_checked : acceptsGraphIso
    (source (graph core1636) (root 9) 1 0) DegreeOneSmallSpectrum1831.graph sourceMap1636swap=true := by decide +kernel
theorem fusedMap1636swap_checked : acceptsGraphIso
    (fused (graph core1636) (root 9) 1 0) DegreeOneSmallSpectrum1138.graph fusedMap1636swap=true := by decide +kernel
theorem certified1636swap : Certified (graph core1636) (root 9) 1 0 :=
  of_native_maps core1636 DegreeOneSmallSpectrum1831.graph DegreeOneSmallSpectrum1138.graph
    sourceMap1636swap fusedMap1636swap sourceMap1636swap_checked fusedMap1636swap_checked
    DegreeOneSmallComparisons.comparison1636
#print axioms sourceMap1636swap_checked
#print axioms fusedMap1636swap_checked
#print axioms certified1636swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
