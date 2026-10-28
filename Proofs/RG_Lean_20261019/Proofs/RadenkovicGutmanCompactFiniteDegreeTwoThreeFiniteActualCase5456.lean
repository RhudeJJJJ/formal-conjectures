/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5456 : Family 3 := level3.get ⟨3,by decide⟩
def sourceMap5456 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 2) → Fin 7 :=
  fun v => ![0,1,2,3,4,5,6] (sourceLabel 3 0 1 v)
def fusedMap5456 : (Vertices 3 ⊕ Fin 3) → Fin 7 :=
  fun v => ![1,2,3,4,0,5,6] (fusedLabel 3 0 1 v)
theorem sourceMap5456_checked : acceptsGraphIso
    (source (graph core5456) (root 3) 0 1) SmallGeFourSpectrum000.graph sourceMap5456=true := by decide +kernel
theorem fusedMap5456_checked : acceptsGraphIso
    (fused (graph core5456) (root 3) 0 1) DegreeOneSmallSpectrum012.graph fusedMap5456=true := by decide +kernel
theorem certified5456 : Certified (graph core5456) (root 3) 0 1 :=
  of_native_maps core5456 SmallGeFourSpectrum000.graph DegreeOneSmallSpectrum012.graph
    sourceMap5456 fusedMap5456 sourceMap5456_checked fusedMap5456_checked
    DegreeTwoThreeFiniteComparisons.comparison5456
#print axioms sourceMap5456_checked
#print axioms fusedMap5456_checked
#print axioms certified5456
def sourceMap5456swap : (Vertices 3 ⊕ Fin 2 ⊕ Fin 1) → Fin 7 :=
  fun v => ![0,1,2,3,5,6,4] (sourceLabel 3 1 0 v)
def fusedMap5456swap : (Vertices 3 ⊕ Fin 3) → Fin 7 :=
  fun v => ![1,2,3,4,0,5,6] (fusedLabel 3 1 0 v)
theorem sourceMap5456swap_checked : acceptsGraphIso
    (source (graph core5456) (root 3) 1 0) SmallGeFourSpectrum000.graph sourceMap5456swap=true := by decide +kernel
theorem fusedMap5456swap_checked : acceptsGraphIso
    (fused (graph core5456) (root 3) 1 0) DegreeOneSmallSpectrum012.graph fusedMap5456swap=true := by decide +kernel
theorem certified5456swap : Certified (graph core5456) (root 3) 1 0 :=
  of_native_maps core5456 SmallGeFourSpectrum000.graph DegreeOneSmallSpectrum012.graph
    sourceMap5456swap fusedMap5456swap sourceMap5456swap_checked fusedMap5456swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5456
#print axioms sourceMap5456swap_checked
#print axioms fusedMap5456swap_checked
#print axioms certified5456swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
