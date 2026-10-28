/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5495 : Family 5 := level5.get ⟨12,by decide⟩
def sourceMap5495 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,10,11,4,5,6,7,8,9] (sourceLabel 5 2 2 v)
def fusedMap5495 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 2 2 v)
theorem sourceMap5495_checked : acceptsGraphIso
    (source (graph core5495) (root 5) 2 2) SmallGeFourSpectrum192.graph sourceMap5495=true := by decide +kernel
theorem fusedMap5495_checked : acceptsGraphIso
    (fused (graph core5495) (root 5) 2 2) DegreeOneSmallSpectrum388.graph fusedMap5495=true := by decide +kernel
theorem certified5495 : Certified (graph core5495) (root 5) 2 2 :=
  of_native_maps core5495 SmallGeFourSpectrum192.graph DegreeOneSmallSpectrum388.graph
    sourceMap5495 fusedMap5495 sourceMap5495_checked fusedMap5495_checked
    DegreeTwoThreeFiniteComparisons.comparison5495
#print axioms sourceMap5495_checked
#print axioms fusedMap5495_checked
#print axioms certified5495
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
