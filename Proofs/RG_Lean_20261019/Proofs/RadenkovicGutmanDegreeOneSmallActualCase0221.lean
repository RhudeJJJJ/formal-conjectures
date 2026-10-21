/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0221 : Family 5 := level5.get ⟨6,by decide⟩
def sourceMap0221 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,9,6,7,8] (sourceLabel 5 0 2 v)
def fusedMap0221 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 0 2 v)
theorem sourceMap0221_checked : acceptsGraphIso
    (source (graph core0221) (root 5) 0 2) DegreeOneSmallSpectrum121.graph sourceMap0221=true := by decide +kernel
theorem fusedMap0221_checked : acceptsGraphIso
    (fused (graph core0221) (root 5) 0 2) DegreeOneSmallSpectrum075.graph fusedMap0221=true := by decide +kernel
theorem certified0221 : Certified (graph core0221) (root 5) 0 2 :=
  of_native_maps core0221 DegreeOneSmallSpectrum121.graph DegreeOneSmallSpectrum075.graph
    sourceMap0221 fusedMap0221 sourceMap0221_checked fusedMap0221_checked
    DegreeOneSmallComparisons.comparison0221
#print axioms sourceMap0221_checked
#print axioms fusedMap0221_checked
#print axioms certified0221
def sourceMap0221swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 5 2 0 v)
def fusedMap0221swap : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 2 0 v)
theorem sourceMap0221swap_checked : acceptsGraphIso
    (source (graph core0221) (root 5) 2 0) DegreeOneSmallSpectrum121.graph sourceMap0221swap=true := by decide +kernel
theorem fusedMap0221swap_checked : acceptsGraphIso
    (fused (graph core0221) (root 5) 2 0) DegreeOneSmallSpectrum075.graph fusedMap0221swap=true := by decide +kernel
theorem certified0221swap : Certified (graph core0221) (root 5) 2 0 :=
  of_native_maps core0221 DegreeOneSmallSpectrum121.graph DegreeOneSmallSpectrum075.graph
    sourceMap0221swap fusedMap0221swap sourceMap0221swap_checked fusedMap0221swap_checked
    DegreeOneSmallComparisons.comparison0221
#print axioms sourceMap0221swap_checked
#print axioms fusedMap0221swap_checked
#print axioms certified0221swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
