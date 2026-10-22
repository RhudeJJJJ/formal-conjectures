/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0494 : Family 10 := level10.get ⟨380,by decide⟩
def sourceMap0494 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0494 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0494_checked : acceptsGraphIso
    (source (graph core0494) (root 10) 0 0) DegreeOneSmallSpectrum1076.graph sourceMap0494=true := by decide +kernel
theorem fusedMap0494_checked : acceptsGraphIso
    (fused (graph core0494) (root 10) 0 0) DegreeOneSmallSpectrum1445.graph fusedMap0494=true := by decide +kernel
theorem certified0494 : Certified (graph core0494) (root 10) 0 0 :=
  of_native_maps core0494 DegreeOneSmallSpectrum1076.graph DegreeOneSmallSpectrum1445.graph
    sourceMap0494 fusedMap0494 sourceMap0494_checked fusedMap0494_checked
    DegreeTwoThreeFiniteComparisons.comparison0494
#print axioms sourceMap0494_checked
#print axioms fusedMap0494_checked
#print axioms certified0494
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
