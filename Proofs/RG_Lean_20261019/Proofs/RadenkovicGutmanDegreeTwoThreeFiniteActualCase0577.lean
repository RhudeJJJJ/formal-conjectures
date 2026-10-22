/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0577 : Family 10 := level10.get ⟨631,by decide⟩
def sourceMap0577 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0577 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0577_checked : acceptsGraphIso
    (source (graph core0577) (root 10) 0 0) DegreeOneSmallSpectrum1205.graph sourceMap0577=true := by decide +kernel
theorem fusedMap0577_checked : acceptsGraphIso
    (fused (graph core0577) (root 10) 0 0) DegreeOneSmallSpectrum1204.graph fusedMap0577=true := by decide +kernel
theorem certified0577 : Certified (graph core0577) (root 10) 0 0 :=
  of_native_maps core0577 DegreeOneSmallSpectrum1205.graph DegreeOneSmallSpectrum1204.graph
    sourceMap0577 fusedMap0577 sourceMap0577_checked fusedMap0577_checked
    DegreeTwoThreeFiniteComparisons.comparison0577
#print axioms sourceMap0577_checked
#print axioms fusedMap0577_checked
#print axioms certified0577
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
