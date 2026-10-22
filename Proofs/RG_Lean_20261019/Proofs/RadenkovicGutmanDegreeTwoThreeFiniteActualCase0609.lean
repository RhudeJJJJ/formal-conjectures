/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0609 : Family 10 := level10.get ⟨719,by decide⟩
def sourceMap0609 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,8,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0609 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0609_checked : acceptsGraphIso
    (source (graph core0609) (root 10) 0 0) DegreeOneSmallSpectrum1334.graph sourceMap0609=true := by decide +kernel
theorem fusedMap0609_checked : acceptsGraphIso
    (fused (graph core0609) (root 10) 0 0) DegreeOneSmallSpectrum1324.graph fusedMap0609=true := by decide +kernel
theorem certified0609 : Certified (graph core0609) (root 10) 0 0 :=
  of_native_maps core0609 DegreeOneSmallSpectrum1334.graph DegreeOneSmallSpectrum1324.graph
    sourceMap0609 fusedMap0609 sourceMap0609_checked fusedMap0609_checked
    DegreeTwoThreeFiniteComparisons.comparison0609
#print axioms sourceMap0609_checked
#print axioms fusedMap0609_checked
#print axioms certified0609
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
