/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0040 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0040 : (Vertices 2 ⊕ Fin 2 ⊕ Fin 3) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (sourceLabel 2 1 2 v)
def fusedMap0040 : (Vertices 2 ⊕ Fin 5) → Fin 8 :=
  fun v => ![1,2,3,0,4,5,6,7] (fusedLabel 2 1 2 v)
theorem sourceMap0040_checked : acceptsGraphIso
    (source (graph core0040) (root 2) 1 2) DegreeOneSmallSpectrum022.graph sourceMap0040=true := by decide +kernel
theorem fusedMap0040_checked : acceptsGraphIso
    (fused (graph core0040) (root 2) 1 2) DegreeOneSmallSpectrum016.graph fusedMap0040=true := by decide +kernel
theorem certified0040 : Certified (graph core0040) (root 2) 1 2 :=
  of_native_maps core0040 DegreeOneSmallSpectrum022.graph DegreeOneSmallSpectrum016.graph
    sourceMap0040 fusedMap0040 sourceMap0040_checked fusedMap0040_checked
    DegreeOneSmallComparisons.comparison0040
#print axioms sourceMap0040_checked
#print axioms fusedMap0040_checked
#print axioms certified0040
def sourceMap0040swap : (Vertices 2 ⊕ Fin 3 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,1,2,5,6,7,3,4] (sourceLabel 2 2 1 v)
def fusedMap0040swap : (Vertices 2 ⊕ Fin 5) → Fin 8 :=
  fun v => ![1,2,3,0,4,5,6,7] (fusedLabel 2 2 1 v)
theorem sourceMap0040swap_checked : acceptsGraphIso
    (source (graph core0040) (root 2) 2 1) DegreeOneSmallSpectrum022.graph sourceMap0040swap=true := by decide +kernel
theorem fusedMap0040swap_checked : acceptsGraphIso
    (fused (graph core0040) (root 2) 2 1) DegreeOneSmallSpectrum016.graph fusedMap0040swap=true := by decide +kernel
theorem certified0040swap : Certified (graph core0040) (root 2) 2 1 :=
  of_native_maps core0040 DegreeOneSmallSpectrum022.graph DegreeOneSmallSpectrum016.graph
    sourceMap0040swap fusedMap0040swap sourceMap0040swap_checked fusedMap0040swap_checked
    DegreeOneSmallComparisons.comparison0040
#print axioms sourceMap0040swap_checked
#print axioms fusedMap0040swap_checked
#print axioms certified0040swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
