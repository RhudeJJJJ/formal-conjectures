/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0884 : Family 8 := level8.get ⟨48,by decide⟩
def sourceMap0884 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,5,0,1,2,3,4,10,11,9,7,8] (sourceLabel 8 0 1 v)
def fusedMap0884 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (fusedLabel 8 0 1 v)
theorem sourceMap0884_checked : acceptsGraphIso
    (source (graph core0884) (root 8) 0 1) DegreeOneSmallSpectrum487.graph sourceMap0884=true := by decide +kernel
theorem fusedMap0884_checked : acceptsGraphIso
    (fused (graph core0884) (root 8) 0 1) DegreeOneSmallSpectrum498.graph fusedMap0884=true := by decide +kernel
theorem certified0884 : Certified (graph core0884) (root 8) 0 1 :=
  of_native_maps core0884 DegreeOneSmallSpectrum487.graph DegreeOneSmallSpectrum498.graph
    sourceMap0884 fusedMap0884 sourceMap0884_checked fusedMap0884_checked
    DegreeOneSmallComparisons.comparison0884
#print axioms sourceMap0884_checked
#print axioms fusedMap0884_checked
#print axioms certified0884
def sourceMap0884swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,5,0,1,2,3,4,10,11,7,8,9] (sourceLabel 8 1 0 v)
def fusedMap0884swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (fusedLabel 8 1 0 v)
theorem sourceMap0884swap_checked : acceptsGraphIso
    (source (graph core0884) (root 8) 1 0) DegreeOneSmallSpectrum487.graph sourceMap0884swap=true := by decide +kernel
theorem fusedMap0884swap_checked : acceptsGraphIso
    (fused (graph core0884) (root 8) 1 0) DegreeOneSmallSpectrum498.graph fusedMap0884swap=true := by decide +kernel
theorem certified0884swap : Certified (graph core0884) (root 8) 1 0 :=
  of_native_maps core0884 DegreeOneSmallSpectrum487.graph DegreeOneSmallSpectrum498.graph
    sourceMap0884swap fusedMap0884swap sourceMap0884swap_checked fusedMap0884swap_checked
    DegreeOneSmallComparisons.comparison0884
#print axioms sourceMap0884swap_checked
#print axioms fusedMap0884swap_checked
#print axioms certified0884swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
