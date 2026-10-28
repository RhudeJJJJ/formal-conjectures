/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5441 : Family 7 := level7.get ⟨57,by decide⟩
def sourceMap5441 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,7,8,9,6,2,3,4,5] (sourceLabel 7 0 0 v)
def fusedMap5441 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,4,5,2,3] (fusedLabel 7 0 0 v)
theorem sourceMap5441_checked : acceptsGraphIso
    (source (graph core5441) (root 7) 0 0) DegreeOneSmallSpectrum093.graph sourceMap5441=true := by decide +kernel
theorem fusedMap5441_checked : acceptsGraphIso
    (fused (graph core5441) (root 7) 0 0) DegreeOneSmallSpectrum142.graph fusedMap5441=true := by decide +kernel
theorem certified5441 : Certified (graph core5441) (root 7) 0 0 :=
  of_native_maps core5441 DegreeOneSmallSpectrum093.graph DegreeOneSmallSpectrum142.graph
    sourceMap5441 fusedMap5441 sourceMap5441_checked fusedMap5441_checked
    DegreeTwoThreeFiniteComparisons.comparison5441
#print axioms sourceMap5441_checked
#print axioms fusedMap5441_checked
#print axioms certified5441
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
