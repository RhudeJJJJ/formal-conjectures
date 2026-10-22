/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0386 : Family 9 := level9.get ⟨644,by decide⟩
def sourceMap0386 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0386 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0386_checked : acceptsGraphIso
    (source (graph core0386) (root 9) 0 0) DegreeOneSmallSpectrum647.graph sourceMap0386=true := by decide +kernel
theorem fusedMap0386_checked : acceptsGraphIso
    (fused (graph core0386) (root 9) 0 0) DegreeOneSmallSpectrum638.graph fusedMap0386=true := by decide +kernel
theorem certified0386 : Certified (graph core0386) (root 9) 0 0 :=
  of_native_maps core0386 DegreeOneSmallSpectrum647.graph DegreeOneSmallSpectrum638.graph
    sourceMap0386 fusedMap0386 sourceMap0386_checked fusedMap0386_checked
    DegreeTwoThreeFiniteComparisons.comparison0386
#print axioms sourceMap0386_checked
#print axioms fusedMap0386_checked
#print axioms certified0386
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
