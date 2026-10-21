/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1740 : Family 9 := level9.get ⟨562,by decide⟩
def sourceMap1740 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1740 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1740_checked : acceptsGraphIso
    (source (graph core1740) (root 9) 0 1) DegreeOneSmallSpectrum1608.graph sourceMap1740=true := by decide +kernel
theorem fusedMap1740_checked : acceptsGraphIso
    (fused (graph core1740) (root 9) 0 1) DegreeOneSmallSpectrum1609.graph fusedMap1740=true := by decide +kernel
theorem certified1740 : Certified (graph core1740) (root 9) 0 1 :=
  of_native_maps core1740 DegreeOneSmallSpectrum1608.graph DegreeOneSmallSpectrum1609.graph
    sourceMap1740 fusedMap1740 sourceMap1740_checked fusedMap1740_checked
    DegreeOneSmallComparisons.comparison1740
#print axioms sourceMap1740_checked
#print axioms fusedMap1740_checked
#print axioms certified1740
def sourceMap1740swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1740swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1740swap_checked : acceptsGraphIso
    (source (graph core1740) (root 9) 1 0) DegreeOneSmallSpectrum1608.graph sourceMap1740swap=true := by decide +kernel
theorem fusedMap1740swap_checked : acceptsGraphIso
    (fused (graph core1740) (root 9) 1 0) DegreeOneSmallSpectrum1609.graph fusedMap1740swap=true := by decide +kernel
theorem certified1740swap : Certified (graph core1740) (root 9) 1 0 :=
  of_native_maps core1740 DegreeOneSmallSpectrum1608.graph DegreeOneSmallSpectrum1609.graph
    sourceMap1740swap fusedMap1740swap sourceMap1740swap_checked fusedMap1740swap_checked
    DegreeOneSmallComparisons.comparison1740
#print axioms sourceMap1740swap_checked
#print axioms fusedMap1740swap_checked
#print axioms certified1740swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
