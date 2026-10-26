/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3755 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap3755 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 5 1 1 v)
def fusedMap3755 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9] (fusedLabel 5 1 1 v)
theorem sourceMap3755_checked : acceptsGraphIso
    (source (graph core3755) (root 5) 1 1) DegreeOneSmallSpectrum161.graph sourceMap3755=true := by decide +kernel
theorem fusedMap3755_checked : acceptsGraphIso
    (fused (graph core3755) (root 5) 1 1) DegreeOneSmallSpectrum111.graph fusedMap3755=true := by decide +kernel
theorem certified3755 : Certified (graph core3755) (root 5) 1 1 :=
  of_native_maps core3755 DegreeOneSmallSpectrum161.graph DegreeOneSmallSpectrum111.graph
    sourceMap3755 fusedMap3755 sourceMap3755_checked fusedMap3755_checked
    DegreeTwoThreeFiniteComparisons.comparison3755
#print axioms sourceMap3755_checked
#print axioms fusedMap3755_checked
#print axioms certified3755
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
