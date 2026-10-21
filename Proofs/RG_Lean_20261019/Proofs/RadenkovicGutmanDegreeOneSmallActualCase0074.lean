/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0074 : Family 3 := level3.get ⟨0,by decide⟩
def sourceMap0074 : (Vertices 3 ⊕ Fin 4 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,5,6,7,1,2,3,4,8,9,10,11,12] (sourceLabel 3 3 4 v)
def fusedMap0074 : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 3 4 v)
theorem sourceMap0074_checked : acceptsGraphIso
    (source (graph core0074) (root 3) 3 4) DegreeOneSmallSpectrum967.graph sourceMap0074=true := by decide +kernel
theorem fusedMap0074_checked : acceptsGraphIso
    (fused (graph core0074) (root 3) 3 4) DegreeOneSmallSpectrum861.graph fusedMap0074=true := by decide +kernel
theorem certified0074 : Certified (graph core0074) (root 3) 3 4 :=
  of_native_maps core0074 DegreeOneSmallSpectrum967.graph DegreeOneSmallSpectrum861.graph
    sourceMap0074 fusedMap0074 sourceMap0074_checked fusedMap0074_checked
    DegreeOneSmallComparisons.comparison0074
#print axioms sourceMap0074_checked
#print axioms fusedMap0074_checked
#print axioms certified0074
def sourceMap0074swap : (Vertices 3 ⊕ Fin 5 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,5,6,7,8,9,10,11,12,1,2,3,4] (sourceLabel 3 4 3 v)
def fusedMap0074swap : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 4 3 v)
theorem sourceMap0074swap_checked : acceptsGraphIso
    (source (graph core0074) (root 3) 4 3) DegreeOneSmallSpectrum967.graph sourceMap0074swap=true := by decide +kernel
theorem fusedMap0074swap_checked : acceptsGraphIso
    (fused (graph core0074) (root 3) 4 3) DegreeOneSmallSpectrum861.graph fusedMap0074swap=true := by decide +kernel
theorem certified0074swap : Certified (graph core0074) (root 3) 4 3 :=
  of_native_maps core0074 DegreeOneSmallSpectrum967.graph DegreeOneSmallSpectrum861.graph
    sourceMap0074swap fusedMap0074swap sourceMap0074swap_checked fusedMap0074swap_checked
    DegreeOneSmallComparisons.comparison0074
#print axioms sourceMap0074swap_checked
#print axioms fusedMap0074swap_checked
#print axioms certified0074swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
