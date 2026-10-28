/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5451 : Family 7 := level7.get ⟨97,by decide⟩
def sourceMap5451 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,7,8,9,1,2,3,4,5,6] (sourceLabel 7 0 0 v)
def fusedMap5451 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,7,8,9,1,2,3,4,5,6] (fusedLabel 7 0 0 v)
theorem sourceMap5451_checked : acceptsGraphIso
    (source (graph core5451) (root 7) 0 0) SmallGeFourSpectrum019.graph sourceMap5451=true := by decide +kernel
theorem fusedMap5451_checked : acceptsGraphIso
    (fused (graph core5451) (root 7) 0 0) DegreeOneSmallSpectrum130.graph fusedMap5451=true := by decide +kernel
theorem certified5451 : Certified (graph core5451) (root 7) 0 0 :=
  of_native_maps core5451 SmallGeFourSpectrum019.graph DegreeOneSmallSpectrum130.graph
    sourceMap5451 fusedMap5451 sourceMap5451_checked fusedMap5451_checked
    DegreeTwoThreeFiniteComparisons.comparison5451
#print axioms sourceMap5451_checked
#print axioms fusedMap5451_checked
#print axioms certified5451
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
