/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0619 : Family 10 := level10.get ⟨749,by decide⟩
def sourceMap0619 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0619 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0619_checked : acceptsGraphIso
    (source (graph core0619) (root 10) 0 0) DegreeTwoThreeSpectrum1153.graph sourceMap0619=true := by decide +kernel
theorem fusedMap0619_checked : acceptsGraphIso
    (fused (graph core0619) (root 10) 0 0) DegreeOneSmallSpectrum1334.graph fusedMap0619=true := by decide +kernel
theorem certified0619 : Certified (graph core0619) (root 10) 0 0 :=
  of_native_maps core0619 DegreeTwoThreeSpectrum1153.graph DegreeOneSmallSpectrum1334.graph
    sourceMap0619 fusedMap0619 sourceMap0619_checked fusedMap0619_checked
    DegreeTwoThreeFiniteComparisons.comparison0619
#print axioms sourceMap0619_checked
#print axioms fusedMap0619_checked
#print axioms certified0619
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
