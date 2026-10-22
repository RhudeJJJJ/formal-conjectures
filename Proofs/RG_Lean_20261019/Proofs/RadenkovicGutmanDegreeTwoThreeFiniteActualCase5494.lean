/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5494 : Family 4 := level4.get ⟨7,by decide⟩
def sourceMap5494 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,7,8,9,10,1,2,3,4,5,6] (sourceLabel 4 2 2 v)
def fusedMap5494 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (fusedLabel 4 2 2 v)
theorem sourceMap5494_checked : acceptsGraphIso
    (source (graph core5494) (root 4) 2 2) SmallGeFourSpectrum067.graph sourceMap5494=true := by decide +kernel
theorem fusedMap5494_checked : acceptsGraphIso
    (fused (graph core5494) (root 4) 2 2) DegreeOneSmallSpectrum207.graph fusedMap5494=true := by decide +kernel
theorem certified5494 : Certified (graph core5494) (root 4) 2 2 :=
  of_native_maps core5494 SmallGeFourSpectrum067.graph DegreeOneSmallSpectrum207.graph
    sourceMap5494 fusedMap5494 sourceMap5494_checked fusedMap5494_checked
    DegreeTwoThreeFiniteComparisons.comparison5494
#print axioms sourceMap5494_checked
#print axioms fusedMap5494_checked
#print axioms certified5494
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
