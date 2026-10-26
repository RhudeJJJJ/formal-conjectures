/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3754 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap3754 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,9,5,6,7,8] (sourceLabel 5 1 1 v)
def fusedMap3754 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9] (fusedLabel 5 1 1 v)
theorem sourceMap3754_checked : acceptsGraphIso
    (source (graph core3754) (root 5) 1 1) DegreeTwoThreeSpectrum148.graph sourceMap3754=true := by decide +kernel
theorem fusedMap3754_checked : acceptsGraphIso
    (fused (graph core3754) (root 5) 1 1) DegreeOneSmallSpectrum101.graph fusedMap3754=true := by decide +kernel
theorem certified3754 : Certified (graph core3754) (root 5) 1 1 :=
  of_native_maps core3754 DegreeTwoThreeSpectrum148.graph DegreeOneSmallSpectrum101.graph
    sourceMap3754 fusedMap3754 sourceMap3754_checked fusedMap3754_checked
    DegreeTwoThreeFiniteComparisons.comparison3754
#print axioms sourceMap3754_checked
#print axioms fusedMap3754_checked
#print axioms certified3754
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
