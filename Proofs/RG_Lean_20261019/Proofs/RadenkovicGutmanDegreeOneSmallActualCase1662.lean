/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1662 : Family 9 := level9.get ⟨419,by decide⟩
def sourceMap1662 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1662 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1662_checked : acceptsGraphIso
    (source (graph core1662) (root 9) 0 1) DegreeOneSmallSpectrum1905.graph sourceMap1662=true := by decide +kernel
theorem fusedMap1662_checked : acceptsGraphIso
    (fused (graph core1662) (root 9) 0 1) DegreeOneSmallSpectrum1298.graph fusedMap1662=true := by decide +kernel
theorem certified1662 : Certified (graph core1662) (root 9) 0 1 :=
  of_native_maps core1662 DegreeOneSmallSpectrum1905.graph DegreeOneSmallSpectrum1298.graph
    sourceMap1662 fusedMap1662 sourceMap1662_checked fusedMap1662_checked
    DegreeOneSmallComparisons.comparison1662
#print axioms sourceMap1662_checked
#print axioms fusedMap1662_checked
#print axioms certified1662
def sourceMap1662swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1662swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1662swap_checked : acceptsGraphIso
    (source (graph core1662) (root 9) 1 0) DegreeOneSmallSpectrum1905.graph sourceMap1662swap=true := by decide +kernel
theorem fusedMap1662swap_checked : acceptsGraphIso
    (fused (graph core1662) (root 9) 1 0) DegreeOneSmallSpectrum1298.graph fusedMap1662swap=true := by decide +kernel
theorem certified1662swap : Certified (graph core1662) (root 9) 1 0 :=
  of_native_maps core1662 DegreeOneSmallSpectrum1905.graph DegreeOneSmallSpectrum1298.graph
    sourceMap1662swap fusedMap1662swap sourceMap1662swap_checked fusedMap1662swap_checked
    DegreeOneSmallComparisons.comparison1662
#print axioms sourceMap1662swap_checked
#print axioms fusedMap1662swap_checked
#print axioms certified1662swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
