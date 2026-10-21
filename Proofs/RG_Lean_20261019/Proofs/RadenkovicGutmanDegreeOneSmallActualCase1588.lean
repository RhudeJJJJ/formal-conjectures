/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1588 : Family 9 := level9.get ⟨330,by decide⟩
def sourceMap1588 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1588 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1588_checked : acceptsGraphIso
    (source (graph core1588) (root 9) 0 1) DegreeOneSmallSpectrum1615.graph sourceMap1588=true := by decide +kernel
theorem fusedMap1588_checked : acceptsGraphIso
    (fused (graph core1588) (root 9) 0 1) DegreeOneSmallSpectrum1009.graph fusedMap1588=true := by decide +kernel
theorem certified1588 : Certified (graph core1588) (root 9) 0 1 :=
  of_native_maps core1588 DegreeOneSmallSpectrum1615.graph DegreeOneSmallSpectrum1009.graph
    sourceMap1588 fusedMap1588 sourceMap1588_checked fusedMap1588_checked
    DegreeOneSmallComparisons.comparison1588
#print axioms sourceMap1588_checked
#print axioms fusedMap1588_checked
#print axioms certified1588
def sourceMap1588swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1588swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1588swap_checked : acceptsGraphIso
    (source (graph core1588) (root 9) 1 0) DegreeOneSmallSpectrum1615.graph sourceMap1588swap=true := by decide +kernel
theorem fusedMap1588swap_checked : acceptsGraphIso
    (fused (graph core1588) (root 9) 1 0) DegreeOneSmallSpectrum1009.graph fusedMap1588swap=true := by decide +kernel
theorem certified1588swap : Certified (graph core1588) (root 9) 1 0 :=
  of_native_maps core1588 DegreeOneSmallSpectrum1615.graph DegreeOneSmallSpectrum1009.graph
    sourceMap1588swap fusedMap1588swap sourceMap1588swap_checked fusedMap1588swap_checked
    DegreeOneSmallComparisons.comparison1588
#print axioms sourceMap1588swap_checked
#print axioms fusedMap1588swap_checked
#print axioms certified1588swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
