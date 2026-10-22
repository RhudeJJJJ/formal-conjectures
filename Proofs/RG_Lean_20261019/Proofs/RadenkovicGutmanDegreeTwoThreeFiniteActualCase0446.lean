/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0446 : Family 10 := level10.get ⟨212,by decide⟩
def sourceMap0446 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0446 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0446_checked : acceptsGraphIso
    (source (graph core0446) (root 10) 0 0) DegreeTwoThreeSpectrum866.graph sourceMap0446=true := by decide +kernel
theorem fusedMap0446_checked : acceptsGraphIso
    (fused (graph core0446) (root 10) 0 0) DegreeOneSmallSpectrum1072.graph fusedMap0446=true := by decide +kernel
theorem certified0446 : Certified (graph core0446) (root 10) 0 0 :=
  of_native_maps core0446 DegreeTwoThreeSpectrum866.graph DegreeOneSmallSpectrum1072.graph
    sourceMap0446 fusedMap0446 sourceMap0446_checked fusedMap0446_checked
    DegreeTwoThreeFiniteComparisons.comparison0446
#print axioms sourceMap0446_checked
#print axioms fusedMap0446_checked
#print axioms certified0446
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
