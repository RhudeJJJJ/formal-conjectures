/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0064 : Family 8 := level8.get ⟨7,by decide⟩
def sourceMap0064 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![3,2,1,0,7,8,9,10,4,5,6] (sourceLabel 8 0 0 v)
def fusedMap0064 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (fusedLabel 8 0 0 v)
theorem sourceMap0064_checked : acceptsGraphIso
    (source (graph core0064) (root 8) 0 0) DegreeOneSmallSpectrum175.graph sourceMap0064=true := by decide +kernel
theorem fusedMap0064_checked : acceptsGraphIso
    (fused (graph core0064) (root 8) 0 0) DegreeOneSmallSpectrum165.graph fusedMap0064=true := by decide +kernel
theorem certified0064 : Certified (graph core0064) (root 8) 0 0 :=
  of_native_maps core0064 DegreeOneSmallSpectrum175.graph DegreeOneSmallSpectrum165.graph
    sourceMap0064 fusedMap0064 sourceMap0064_checked fusedMap0064_checked
    DegreeTwoThreeFiniteComparisons.comparison0064
#print axioms sourceMap0064_checked
#print axioms fusedMap0064_checked
#print axioms certified0064
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
