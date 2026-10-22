/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0058 : Family 7 := level7.get ⟨90,by decide⟩
def sourceMap0058 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 7 0 0 v)
def fusedMap0058 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0058_checked : acceptsGraphIso
    (source (graph core0058) (root 7) 0 0) DegreeOneSmallSpectrum145.graph sourceMap0058=true := by decide +kernel
theorem fusedMap0058_checked : acceptsGraphIso
    (fused (graph core0058) (root 7) 0 0) DegreeOneSmallSpectrum144.graph fusedMap0058=true := by decide +kernel
theorem certified0058 : Certified (graph core0058) (root 7) 0 0 :=
  of_native_maps core0058 DegreeOneSmallSpectrum145.graph DegreeOneSmallSpectrum144.graph
    sourceMap0058 fusedMap0058 sourceMap0058_checked fusedMap0058_checked
    DegreeTwoThreeFiniteComparisons.comparison0058
#print axioms sourceMap0058_checked
#print axioms fusedMap0058_checked
#print axioms certified0058
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
