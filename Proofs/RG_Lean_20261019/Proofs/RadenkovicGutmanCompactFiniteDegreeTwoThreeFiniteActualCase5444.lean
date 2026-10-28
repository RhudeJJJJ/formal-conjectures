/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5444 : Family 7 := level7.get ⟨76,by decide⟩
def sourceMap5444 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,2,3,4,5] (sourceLabel 7 0 0 v)
def fusedMap5444 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,8,9,6,7] (fusedLabel 7 0 0 v)
theorem sourceMap5444_checked : acceptsGraphIso
    (source (graph core5444) (root 7) 0 0) DegreeOneSmallSpectrum154.graph sourceMap5444=true := by decide +kernel
theorem fusedMap5444_checked : acceptsGraphIso
    (fused (graph core5444) (root 7) 0 0) DegreeOneSmallSpectrum119.graph fusedMap5444=true := by decide +kernel
theorem certified5444 : Certified (graph core5444) (root 7) 0 0 :=
  of_native_maps core5444 DegreeOneSmallSpectrum154.graph DegreeOneSmallSpectrum119.graph
    sourceMap5444 fusedMap5444 sourceMap5444_checked fusedMap5444_checked
    DegreeTwoThreeFiniteComparisons.comparison5444
#print axioms sourceMap5444_checked
#print axioms fusedMap5444_checked
#print axioms certified5444
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
