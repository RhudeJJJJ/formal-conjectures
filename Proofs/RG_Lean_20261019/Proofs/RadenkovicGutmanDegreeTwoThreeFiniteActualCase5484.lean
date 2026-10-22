/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5484 : Family 5 := level5.get ⟨16,by decide⟩
def sourceMap5484 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (sourceLabel 5 0 5 v)
def fusedMap5484 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 0 5 v)
theorem sourceMap5484_checked : acceptsGraphIso
    (source (graph core5484) (root 5) 0 5) DegreeOneSmallSpectrum1118.graph sourceMap5484=true := by decide +kernel
theorem fusedMap5484_checked : acceptsGraphIso
    (fused (graph core5484) (root 5) 0 5) DegreeOneSmallSpectrum872.graph fusedMap5484=true := by decide +kernel
theorem certified5484 : Certified (graph core5484) (root 5) 0 5 :=
  of_native_maps core5484 DegreeOneSmallSpectrum1118.graph DegreeOneSmallSpectrum872.graph
    sourceMap5484 fusedMap5484 sourceMap5484_checked fusedMap5484_checked
    DegreeTwoThreeFiniteComparisons.comparison5484
#print axioms sourceMap5484_checked
#print axioms fusedMap5484_checked
#print axioms certified5484
def sourceMap5484swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,9,10,11,12,8] (sourceLabel 5 5 0 v)
def fusedMap5484swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 5 0 v)
theorem sourceMap5484swap_checked : acceptsGraphIso
    (source (graph core5484) (root 5) 5 0) DegreeOneSmallSpectrum1118.graph sourceMap5484swap=true := by decide +kernel
theorem fusedMap5484swap_checked : acceptsGraphIso
    (fused (graph core5484) (root 5) 5 0) DegreeOneSmallSpectrum872.graph fusedMap5484swap=true := by decide +kernel
theorem certified5484swap : Certified (graph core5484) (root 5) 5 0 :=
  of_native_maps core5484 DegreeOneSmallSpectrum1118.graph DegreeOneSmallSpectrum872.graph
    sourceMap5484swap fusedMap5484swap sourceMap5484swap_checked fusedMap5484swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5484
#print axioms sourceMap5484swap_checked
#print axioms fusedMap5484swap_checked
#print axioms certified5484swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
