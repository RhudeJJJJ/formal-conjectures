/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5438 : Family 7 := level7.get ⟨25,by decide⟩
def sourceMap5438 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,7,8,9,3,4,5,6] (sourceLabel 7 0 0 v)
def fusedMap5438 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,4,5,2,3] (fusedLabel 7 0 0 v)
theorem sourceMap5438_checked : acceptsGraphIso
    (source (graph core5438) (root 7) 0 0) SmallGeFourSpectrum016.graph sourceMap5438=true := by decide +kernel
theorem fusedMap5438_checked : acceptsGraphIso
    (fused (graph core5438) (root 7) 0 0) DegreeOneSmallSpectrum082.graph fusedMap5438=true := by decide +kernel
theorem certified5438 : Certified (graph core5438) (root 7) 0 0 :=
  of_native_maps core5438 SmallGeFourSpectrum016.graph DegreeOneSmallSpectrum082.graph
    sourceMap5438 fusedMap5438 sourceMap5438_checked fusedMap5438_checked
    DegreeTwoThreeFiniteComparisons.comparison5438
#print axioms sourceMap5438_checked
#print axioms fusedMap5438_checked
#print axioms certified5438
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
