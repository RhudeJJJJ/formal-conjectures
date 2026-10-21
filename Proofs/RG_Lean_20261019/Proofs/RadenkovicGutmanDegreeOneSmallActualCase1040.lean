/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1040 : Family 8 := level8.get ⟨116,by decide⟩
def sourceMap1040 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,9,7,8] (sourceLabel 8 0 1 v)
def fusedMap1040 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1040_checked : acceptsGraphIso
    (source (graph core1040) (root 8) 0 1) DegreeOneSmallSpectrum740.graph sourceMap1040=true := by decide +kernel
theorem fusedMap1040_checked : acceptsGraphIso
    (fused (graph core1040) (root 8) 0 1) DegreeOneSmallSpectrum442.graph fusedMap1040=true := by decide +kernel
theorem certified1040 : Certified (graph core1040) (root 8) 0 1 :=
  of_native_maps core1040 DegreeOneSmallSpectrum740.graph DegreeOneSmallSpectrum442.graph
    sourceMap1040 fusedMap1040 sourceMap1040_checked fusedMap1040_checked
    DegreeOneSmallComparisons.comparison1040
#print axioms sourceMap1040_checked
#print axioms fusedMap1040_checked
#print axioms certified1040
def sourceMap1040swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 8 1 0 v)
def fusedMap1040swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1040swap_checked : acceptsGraphIso
    (source (graph core1040) (root 8) 1 0) DegreeOneSmallSpectrum740.graph sourceMap1040swap=true := by decide +kernel
theorem fusedMap1040swap_checked : acceptsGraphIso
    (fused (graph core1040) (root 8) 1 0) DegreeOneSmallSpectrum442.graph fusedMap1040swap=true := by decide +kernel
theorem certified1040swap : Certified (graph core1040) (root 8) 1 0 :=
  of_native_maps core1040 DegreeOneSmallSpectrum740.graph DegreeOneSmallSpectrum442.graph
    sourceMap1040swap fusedMap1040swap sourceMap1040swap_checked fusedMap1040swap_checked
    DegreeOneSmallComparisons.comparison1040
#print axioms sourceMap1040swap_checked
#print axioms fusedMap1040swap_checked
#print axioms certified1040swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
