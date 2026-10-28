/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5434 : Family 6 := level6.get ⟨35,by decide⟩
def sourceMap5434 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,6,7,8,1,2,3,4,5] (sourceLabel 6 0 0 v)
def fusedMap5434 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,6,7,8,1,2,5,3,4] (fusedLabel 6 0 0 v)
theorem sourceMap5434_checked : acceptsGraphIso
    (source (graph core5434) (root 6) 0 0) SmallGeFourSpectrum007.graph sourceMap5434=true := by decide +kernel
theorem fusedMap5434_checked : acceptsGraphIso
    (fused (graph core5434) (root 6) 0 0) DegreeOneSmallSpectrum053.graph fusedMap5434=true := by decide +kernel
theorem certified5434 : Certified (graph core5434) (root 6) 0 0 :=
  of_native_maps core5434 SmallGeFourSpectrum007.graph DegreeOneSmallSpectrum053.graph
    sourceMap5434 fusedMap5434 sourceMap5434_checked fusedMap5434_checked
    DegreeTwoThreeFiniteComparisons.comparison5434
#print axioms sourceMap5434_checked
#print axioms fusedMap5434_checked
#print axioms certified5434
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
