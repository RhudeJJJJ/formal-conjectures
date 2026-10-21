/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1672 : Family 9 := level9.get ⟨428,by decide⟩
def sourceMap1672 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (sourceLabel 9 0 1 v)
def fusedMap1672 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1672_checked : acceptsGraphIso
    (source (graph core1672) (root 9) 0 1) DegreeOneSmallSpectrum1924.graph sourceMap1672=true := by decide +kernel
theorem fusedMap1672_checked : acceptsGraphIso
    (fused (graph core1672) (root 9) 0 1) DegreeOneSmallSpectrum1316.graph fusedMap1672=true := by decide +kernel
theorem certified1672 : Certified (graph core1672) (root 9) 0 1 :=
  of_native_maps core1672 DegreeOneSmallSpectrum1924.graph DegreeOneSmallSpectrum1316.graph
    sourceMap1672 fusedMap1672 sourceMap1672_checked fusedMap1672_checked
    DegreeOneSmallComparisons.comparison1672
#print axioms sourceMap1672_checked
#print axioms fusedMap1672_checked
#print axioms certified1672
def sourceMap1672swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 9 1 0 v)
def fusedMap1672swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1672swap_checked : acceptsGraphIso
    (source (graph core1672) (root 9) 1 0) DegreeOneSmallSpectrum1924.graph sourceMap1672swap=true := by decide +kernel
theorem fusedMap1672swap_checked : acceptsGraphIso
    (fused (graph core1672) (root 9) 1 0) DegreeOneSmallSpectrum1316.graph fusedMap1672swap=true := by decide +kernel
theorem certified1672swap : Certified (graph core1672) (root 9) 1 0 :=
  of_native_maps core1672 DegreeOneSmallSpectrum1924.graph DegreeOneSmallSpectrum1316.graph
    sourceMap1672swap fusedMap1672swap sourceMap1672swap_checked fusedMap1672swap_checked
    DegreeOneSmallComparisons.comparison1672
#print axioms sourceMap1672swap_checked
#print axioms fusedMap1672swap_checked
#print axioms certified1672swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
