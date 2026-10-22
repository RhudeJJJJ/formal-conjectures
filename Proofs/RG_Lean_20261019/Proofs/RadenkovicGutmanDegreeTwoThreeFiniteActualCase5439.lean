/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5439 : Family 7 := level7.get ⟨38,by decide⟩
def sourceMap5439 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,2,3,4,5] (sourceLabel 7 0 0 v)
def fusedMap5439 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,8,9,6,7] (fusedLabel 7 0 0 v)
theorem sourceMap5439_checked : acceptsGraphIso
    (source (graph core5439) (root 7) 0 0) DegreeOneSmallSpectrum094.graph sourceMap5439=true := by decide +kernel
theorem fusedMap5439_checked : acceptsGraphIso
    (fused (graph core5439) (root 7) 0 0) DegreeOneSmallSpectrum126.graph fusedMap5439=true := by decide +kernel
theorem certified5439 : Certified (graph core5439) (root 7) 0 0 :=
  of_native_maps core5439 DegreeOneSmallSpectrum094.graph DegreeOneSmallSpectrum126.graph
    sourceMap5439 fusedMap5439 sourceMap5439_checked fusedMap5439_checked
    DegreeTwoThreeFiniteComparisons.comparison5439
#print axioms sourceMap5439_checked
#print axioms fusedMap5439_checked
#print axioms certified5439
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
