/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0010 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap0010 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 1) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (sourceLabel 5 0 0 v)
def fusedMap0010 : (Vertices 5 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (fusedLabel 5 0 0 v)
theorem sourceMap0010_checked : acceptsGraphIso
    (source (graph core0010) (root 5) 0 0) DegreeOneSmallSpectrum033.graph sourceMap0010=true := by decide +kernel
theorem fusedMap0010_checked : acceptsGraphIso
    (fused (graph core0010) (root 5) 0 0) DegreeOneSmallSpectrum032.graph fusedMap0010=true := by decide +kernel
theorem certified0010 : Certified (graph core0010) (root 5) 0 0 :=
  of_native_maps core0010 DegreeOneSmallSpectrum033.graph DegreeOneSmallSpectrum032.graph
    sourceMap0010 fusedMap0010 sourceMap0010_checked fusedMap0010_checked
    DegreeTwoThreeFiniteComparisons.comparison0010
#print axioms sourceMap0010_checked
#print axioms fusedMap0010_checked
#print axioms certified0010
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
