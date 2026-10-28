/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5446 : Family 7 := level7.get ⟨85,by decide⟩
def sourceMap5446 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,2,3,4,5] (sourceLabel 7 0 0 v)
def fusedMap5446 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,8,9,6,7] (fusedLabel 7 0 0 v)
theorem sourceMap5446_checked : acceptsGraphIso
    (source (graph core5446) (root 7) 0 0) DegreeOneSmallSpectrum155.graph sourceMap5446=true := by decide +kernel
theorem fusedMap5446_checked : acceptsGraphIso
    (fused (graph core5446) (root 7) 0 0) DegreeOneSmallSpectrum135.graph fusedMap5446=true := by decide +kernel
theorem certified5446 : Certified (graph core5446) (root 7) 0 0 :=
  of_native_maps core5446 DegreeOneSmallSpectrum155.graph DegreeOneSmallSpectrum135.graph
    sourceMap5446 fusedMap5446 sourceMap5446_checked fusedMap5446_checked
    DegreeTwoThreeFiniteComparisons.comparison5446
#print axioms sourceMap5446_checked
#print axioms fusedMap5446_checked
#print axioms certified5446
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
